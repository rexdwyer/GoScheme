package main

import "fmt"
import "strings"
import "strconv"
import "errors"
import "os"
import "flag"

// Characters that can appear in atome.
const alpha = "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ+-*/=><"


var pFlag bool // If true, use parallel evlis.  Set on command line.


// The fundamental S-expression data structure.
type SexprRec struct {
	name     *string  // If it's an atom, this will point to name; else nil.
	car, cdr Sexpr    // If it's not an atom, these will not be nil.
}
type Sexpr *SexprRec

// functions for creating atoms.
func newAtom(name string) Sexpr {
	return &SexprRec{&name, nil, nil}
}

func nyl() Sexpr {
	return newAtom("nil")
}

func t() Sexpr {
	return newAtom("t")
}

// Lisp primitives
func atom(s Sexpr) bool {
	return (*s).name != nil
}

func null(s Sexpr) bool {
	return ((*s).name != nil && *((*s).name) == "nil")
}

func cons(theCar, theCdr Sexpr) Sexpr {
	return &SexprRec{nil, theCar, theCdr}
}

func cdr(s Sexpr) Sexpr {
	return (*s).cdr
}
func car(s Sexpr) Sexpr {
	return (*s).car
}

// Some useful functions for selecting list elements.
func second(s Sexpr) Sexpr {
	return car(cdr(s))
}

func third(s Sexpr) Sexpr {
	return car(cdr(cdr(s)))
}

func fourth(s Sexpr) Sexpr {
	return car(cdr(cdr(cdr(s))))
}

// Functions for printing an S-expression.
func String(s Sexpr) string {
	if atom(s) {
		return *((*s).name)
	}
	return "(" + StringCdr(s)
}

func StringCdr(s Sexpr) string {
	carString := String(car(s))
	if null(cdr(s)) {
		return carString + ")"
	}
	if atom(cdr(s)) {
		return carString + "." + String(cdr(s)) + ")"
	}
	return carString + " " + StringCdr(cdr(s))
}

// Functions for parsing an S-expression.
// Call this function on the string to be parsed.
func parser(s string) Sexpr {
	return parse(strings.NewReader(s))
}

// Peeks at the next character without consuming it.
func peek(r *strings.Reader) byte {
	b, _ := r.ReadByte()
	r.UnreadByte()
	return b
}

// Reads and consumes the next character.
func read(r *strings.Reader) byte {
	b, _ := r.ReadByte()
	//fmt.Println(string(b))
	return b
}

// Consumes white space.
func skipWhite(r *strings.Reader) {
	b := peek(r)
	for b == ' ' || b == '\n' || b == '\r' || b == '\t' {
		read(r)
		b = peek(r)
	}
}

// Top level for parsing string in a Reader.
func parse(r *strings.Reader) Sexpr {
	skipWhite(r)
	b := peek(r)
	if b == '(' {
		b = read(r)
		return parseCdr(r)
	}
	return (parseAtom(r))
}

// Parses what's level of a list when the ( is removed.
func parseCdr(r *strings.Reader) Sexpr {
	skipWhite(r)
	if peek(r) == ')' { // done with this liet
		read(r)
		return nyl()
	} else { // parse the current expression, then the rest of the list.
		return cons(parse(r), parseCdr(r))
	}
}

// Parses an atom and creates a record.  
// Identifiers can contain most characters that are not white space or a paren.
func parseAtom(r *strings.Reader) Sexpr {
	skipWhite(r)
	s := ""
	// Look for character in master list. -1 means it's not there.
	for strings.IndexByte(alpha, peek(r)) != -1 {
		s += string(read(r)) // A character is not a string. Convert.
	}
	return (newAtom(s))
}

// These are the primitive functions and constants.
// They evaluate to themselves.
func globalEnv() Sexpr {
	consts := parser("(t nil car cdr cons atom null + - * / == > < not and or list prog2 print)")
	return cons(cons(consts, consts), nyl())
}

// Function for looking up a variable (atom) in an environment.
func lookup(atom Sexpr, env Sexpr) Sexpr {
        // for each vertebra...     		 
	for e := env; !null(e); e = cdr(e) {
                // for each variable on rib...
		vars := car(car(e))
		vals := cdr(car(e))
		for !null(vars) {
			if *atom.name == *car(vars).name {
				return car(vals)
			}
			vars = cdr(vars)
			vals = cdr(vals)
		}

	}
	panic(errors.New("No value for " + *atom.name))
}

// Evaluate an expression in the given environment.
// There are various special forms, and function application.
func eval(exp Sexpr, env Sexpr) Sexpr {
     for {
     	// Integers evaluate to themselves.
	if atom(exp) && isInteger(*exp.name) {
		return exp
	}
	// Atoms must be looked up in the environment.
	// Constants are mapped to themselves in the global environment.
	if atom(exp) {
		return lookup(exp, env)
	}
	// quote indicates that its "argument" is not be evaluated.
	if atom(car(exp)) && *car(exp).name == "quote" {
		return second(exp)
	}
	// for list, we evaluate all the arguments and return the list of results.
	if atom(car(exp)) && *car(exp).name == "list" {
		return evlis(cdr(exp), env)
	}
	// for prog2, we evaluate the two arguments in order and return the second.
	if atom(car(exp)) && *car(exp).name == "prog2" {
		eval(second(exp), env)
		exp = third(exp)
		continue
	}
	// for if, we evaluate the first argument then choose either the 2nd or 3rd.
	if atom(car(exp)) && *car(exp).name == "if" {
		if null(eval(second(exp), env)) {
			exp = fourth(exp)
		} else {
		        exp = third(exp)
                }
                continue
	}
	// lambda expressions evaluate to closures, which include the environment
	// in which the function is defined.
	if atom(car(exp)) && *car(exp).name == "lambda" {
		return cons(newAtom("*CLOSURE*"), cons(exp, cons(env, nyl())))
	}
	// letrec defines a set of mutually recursive functions. It's tricky.
	if atom(car(exp)) && *car(exp).name == "letrec" {
		// The new environment will include the new functions, and the
		// new functions will include the new environment.  Therefore, we
		// have to build a circular structure.
		// The environment is a backbone that is a list of vertebrae.
		// Each vertebra holds two ribs:
		// One for function names and one for closures.
		// The ribs get filled in later.
		nyll := nyl()
		vertebra := cons(nyll,nyll)
		newenv := cons(vertebra, env)
		names := nyll;
		vals := nyll;
		// Now step through the function definitions and build up a
		// list of names and a list of closures.
		for pairs := second(exp); !null(pairs); pairs = cdr(pairs) {
			pair := car(pairs)
			name := car(pair)
			val := eval(second(pair), newenv) // close lambda
			names = cons(name, names)
			vals = cons(val, vals)
		}
		// Install the two ribs.
		vertebra.car = names
		vertebra.cdr = vals
		// Last evaluate the body of the letrec in the new extended environment.
                exp,env = third(exp), newenv
		continue
	}
	// It's not an atom and none of the special forms apply, so it's a function
	// application.  Evaluate every element of the list, then apply function.
	lis := evlis(exp, env)
	fun := car(lis)
	args := cdr(lis)
	if atom(fun) {
		return applyPrimitive(*fun.name, args)
	}
	if *car(fun).name == "*CLOSURE*" {
		lambda := second(fun)
		formals := second(lambda)
		body := third(lambda)
		env = third(fun)
		vetebra := cons(formals, args)
		newenv := cons(vetebra, env)
		exp,env = body, newenv
		continue
	}
	panic(errors.New("Illegal function"))
    }
}

// Evaluates a list of expressions in the given environment.
// Prelude to function application.
func evlis(exp Sexpr, env Sexpr) Sexpr {
	if pFlag {
		goList := buildGoList(cdr(exp), env)
		carval := eval(car(exp), env)
		return cons(carval, collectFromGoList(goList))
	}
	return simpleEvlis(exp, env)
}

// This version is for sequential evaluation.
func simpleEvlis(exp Sexpr, env Sexpr) Sexpr {
	if null(exp) {
		return exp // ... that is, nil.
	}
	return cons(eval(car(exp), env), simpleEvlis(cdr(exp), env))
}

// This struct helps us manage parallel evaluation with goroutines.
type goCell struct {
	c    chan bool  // This will be a channel for signaling completion
	exp  Sexpr      // This will hold the result of the evaluation.
	next *goCell    // This points to the cell for the next evaluation.
}

// Function to build a list of goCells and start goroutines for each expression.
func buildGoList(exp Sexpr, env Sexpr) *goCell {
	if null(exp) {
		return nil
	}
	cell := &goCell{make(chan bool), car(exp), buildGoList(cdr(exp), env)}
	go peval(cell, env)
	return cell
}

// The goroutine to evaluate one argument.
func peval(cell *goCell, env Sexpr) {
        // Replace the contents of the cell with its value.     
	cell.exp = eval(cell.exp, env)
	// Signal completion on the channel saved in the cell.
	cell.c <- true
}

// Function to wait for completion of goroutines and collect results into
// S-expression list.
func collectFromGoList(cell *goCell) Sexpr {
	if cell == nil {
		return nyl()
	}
	_ = <-cell.c  // We just want to know it's done. Value is true.
	return cons(cell.exp, collectFromGoList(cell.next))
}

// Evaluate a function application.
// The function and the evaluated arguments are in exp.
// If the function is not a primitive, then we must retrieve the environment
// from the closure and extend it with ribs for the formal parameters and
// actual arguments.

// Apply primitive operations.  They would have evaluated to themselves.
func applyPrimitive(name string, args Sexpr) Sexpr {
	arg1 := car(args)
	if name == "car" {
		return car(arg1)
	}
	if name == "cdr" {
		return cdr(arg1)
	}
	if name == "null" {
		if null(arg1) {
			return t()
		} else {
			return nyl()
		}
	}
	if name == "atom" {
		if atom(arg1) {
			return t()
		} else {
			return nyl()
		}
	}
	if name == "not" {
		if null(arg1) {
			return t()
		} else {
			return nyl()
		}
	}
	// A number can be used as a function.  It selects an element of the list.
	if isInteger(name) && numValue(name) > 0 {
		lis := arg1
		i := numValue(name)
		for ; i > 1; i-- {
			lis = cdr(lis)
		}
		return car(lis)
	}
	if name == "print" {
		fmt.Println(String(arg1))
		return arg1
	}
	arg2 := second(args)
	if name == "cons" {
		return cons(arg1, arg2)
	}
	if name == "and" {
		if null(arg1) {
			return arg1 // nil
		} else {
			return arg2
		}
	}
	if name == "or" {
		if !null(arg1) {
			return arg1
		} else {
			return arg2
		}
	}
	if name == "==" {
		if !atom(arg1) || !atom(arg2) {
			panic(errors.New("== with lists"))
		} else if *arg1.name == *arg2.name {
			return t()
		} else {
			return nyl()
		}
	}
	num1 := numValue(*arg1.name)
	num2 := numValue(*arg2.name)
	if name == "+" || name == "-" || name == "*" || name == "/" {
		return applyArithmetic(name, num1, num2)
	}
	if name == "<" {
		if num1 < num2 {
			return t()
		} else {
			return nyl()
		}
	}
	if name == ">" {
		if num1 > num2 {
			return t()
		} else {
			return nyl()
		}
	}
	panic(errors.New("Couldn't apply primitive " + name))
}

// Apply the arithmetic operators and return an atom for the result.
func applyArithmetic(name string, num1 int, num2 int) Sexpr {
	var ans int
	switch name {
	case "+":
		ans = num1 + num2
	case "-":
		ans = num1 - num2
	case "*":
		ans = num1 * num2
	case "/":
		ans = num1 / num2
	}
	return newAtom(strconv.FormatInt(int64(ans), 10))
}

// The integer value of a number string. It should already be validated.
func numValue(s string) int {
	n, _ := strconv.ParseInt(s, 10, 0)
	return int(n)
}

// Simply asks: Does the string represent an integer?
func isInteger(s string) bool {
	_, err := strconv.ParseInt(s, 10, 0)
	return err == nil
}

// Read the program from stdin, echo it, evaluate it, and print result.
func main() {
	flag.BoolVar(&pFlag, "p", false, "use parallel evlis")
	flag.Parse()
	b := make([]byte, 5000)
	n, err := os.Stdin.Read(b)
	if err != nil {
		panic(err)
	}
	progstring := string(b[:n])
	fmt.Println(progstring)
	fmt.Println(String(eval(parser(progstring),globalEnv())))
}
