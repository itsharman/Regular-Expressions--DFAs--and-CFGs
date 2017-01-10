#lang racket

;****************************************************************
; Name: Harmanpreet Singh
; Email address: harmanpreet.singh@yale.edu
; Topics: strings, languages, regular expressions,
; deterministic finite state acceptors and context free grammars.
;****************************************************************

(provide concat concat? concat-arg1 concat-arg2
         either either? either-arg1 either-arg2
         repeat repeat? repeat-arg1
         ok-string? reg-exp?
         flip pick
         generate-string-from-reg-exp
         dfa dfa? dfa-alphabet dfa-states dfa-start-state dfa-accepting-states dfa-transitions
         entry entry? entry-key entry-value
         dfa-accepts?
         cfg cfg? cfg-terminals cfg-nonterminals cfg-start-symbol cfg-rules
         rule rule? rule-lhs rule-rhs
         leaf leaf? leaf-label
         node node? node-label node-children
         list-leaf-labels
         generate-parse-tree-from-cfg generate-string-from-cfg
         dfa-mcd
         exp-mcd
         my-cfg)

(define hours 4)

; The following structs are used in the representation of Regular Expressions.

(struct concat (arg1 arg2) #:transparent)
(struct either (arg1 arg2) #:transparent)
(struct repeat (arg1) #:transparent)

; A String is a list of Racket symbols.

; A Regular Expression is defined recursively as follows:
; (1) a String is a Regular Expression,
; (2) If exp1 and exp2 are Regular Expressions, then so are
; (concat exp1 exp2), (either exp1 exp2) and (repeat exp1).
; These correspond to concatenation, union ("or"), and Kleene star
; for regular expressions.

; Examples of Regular Expressions
; These are: the empty string, the string abbab, the expression ab(c|d),
; the expression (a|b)*, and the expression ((a|the)((mouse|cat)(ran|slept)))

(define exp1 '())
(define exp2 '(a b b a b))
(define exp3 (concat '(a b) (either '(c) '(d))))
(define exp4 (repeat (either '(a) '(b))))
(define exp5 (concat (either '(a) '(the)) 
                     (concat (either '(mouse) '(cat)) 
                             (either '(ran) '(slept)))))

; The procedure (ok-string? value) takes an arbitrary Racket value
; and returns #t if it is a String (that is, a list of Racket symbols)
; and #f otherwise.
(define (ok-string? value)
   (if (list? value)
      (if (null? value)
          #t
          (if (symbol? (first value))
              (ok-string? (rest value))
              #f))
      #f))

; The procedure (reg-exp? value) takes an arbitrary Racket value
; and returns #t if it is a Regular Expression according to the
; definition given above, and #f otherwise.
(define (reg-exp? value)
  (cond
    [(ok-string? value) #t]
    [(repeat? value) (reg-exp? (repeat-arg1 value))]
    [(concat? value) (and (reg-exp? (concat-arg1 value)) (reg-exp? (concat-arg2 value)))]
    [(either? value) (and (reg-exp? (either-arg1 value)) (reg-exp? (either-arg2 value)))]
    [else #f]))

; The procedure (flip bias) simulates flipping a biased coin, 
; where the bias is specified as a number between 0 and 1,
; and the result is #t with probability equal to the bias 
; and #f with probability (1 - bias).  You can test your procedure
; by making sure that 1000 calls to (flip bias) return about
; 1000*bias values of #t.

(define (flip bias)
  (cond
    [(> (* bias 1000000) (random 1000000)) #t]
    [else #f]))

; The procedure (pick lst) takes a list lst and returns
; a randomly chosen element of lst.  If lst is empty, the
; value returned should be #f.  
; You can test it by picking 10000 times from
; a list with 10 elements, and making sure that each element is
; picked about 1000 times.

(define (pick lst)
  (if (null? lst)
      #f
      (list-ref lst (random (length lst)))))

; The procedure (generate-string-from-reg-exp exp)
; takes a Regular Expression exp and
; returns a random element of the language
; denoted by exp.  Every string in the language
; must have a positive probability of being chosen,
; and every string not in the language must have a
; probability of 0 of being chosen.

(define (generate-string-from-reg-exp exp)
 (cond
    [(ok-string? exp) exp]
    [(concat? exp) (append (generate-string-from-reg-exp (concat-arg1 exp)) (generate-string-from-reg-exp (concat-arg2 exp)))]
    [(either? exp) (generate-string-from-reg-exp (pick (list (either-arg1 exp) (either-arg2 exp))))]
    [(repeat? exp) (if (flip 0.5)
                       '()
                       (generate-string-from-reg-exp (concat (repeat-arg1 exp) exp)))])) 

;************************************************************
; A (possibly incomplete) Deterministic Finite State Acceptor (DFA)
; is represented by the following struct.

(struct dfa (alphabet states start-state accepting-states transitions) #:transparent)

; where alphabet is a list of Racket symbols
; states is a list of Racket symbols
; start-state is one of the elements of states
; accepting-states is a list containing some of the elements of states
; and transitions is a table whose entries
;    have a key that is a list containing a state and a member of the alphabet
;         a value that is a state

(struct entry (key value) #:transparent)

; Examples of DFAs.
; Here is a DFA for the language of all strings of a's and b's with
; an even number of a's and any number of b's.

; equivalent to (b*ab*a)*
(define even-as
  (dfa
    '(a b)
    '(even odd)
    'even
    '(even)
    (list
     (entry '(even a) 'odd)
     (entry '(even b) 'even)
     (entry '(odd a) 'even)
     (entry '(odd b) 'odd))))

; Here is an (incomplete) DFA to accept the language of the
; regular expression c(a|d)(a|d)*r

(define car-cdr
  (dfa
   '(a c d r)
   '(start saw-c saw-a-or-d saw-r)
   'start
   '(saw-r)
   (list
    (entry '(start c) 'saw-c)
    (entry '(saw-c a) 'saw-a-or-d)
    (entry '(saw-c d) 'saw-a-or-d)
    (entry '(saw-a-or-d a) 'saw-a-or-d)
    (entry '(saw-a-or-d d) 'saw-a-or-d)
    (entry '(saw-a-or-d r) 'saw-r))))

; The procedure (dfa-accepts? mach str) takes a DFA mach and
; a String str and determine whether the DFA accepts the String.

(define (dfa-accepts? mach str)
  (define (look-up state str lst)
    (cond
      [(null? lst) #f]
      [(and (equal? (first str) (second (entry-key (first lst))))
            (equal? state (car (entry-key (first lst)))))
              (entry-value (first lst))]
      [else (look-up state str (rest lst))]))

  (define (compute state str)
    (cond
      [(null? str) state]
      [(look-up state str (dfa-transitions mach)) (compute (look-up state str (dfa-transitions mach)) (rest str))]
      [else #f]))

  (if (compute (dfa-start-state mach) str)  
      (if (member (compute (dfa-start-state mach) str) (dfa-accepting-states mach))
          #t
          #f)
      #f))
     
;************************************************************
; A Context Free Grammar (CFG) is represented using the following.

(struct cfg (terminals nonterminals start-symbol rules) #:transparent)

(struct rule (lhs rhs) #:transparent)

; where
; terminals is a list of Racket symbols
; nonterminals is a list of Racket symbols
; (these two lists should have no elements in common)
; start-symbol is an element of the nonterminals list
; rules is a list of rule structs -- each of which has
; a lhs that is an element of the nonterminals list, and
; a rhs that is a list of elements from the terminals or nonterminals list


; Examples of CFGs.

(define grammar-mcd
  (cfg
   '(a the mouse cat dog it slept swam chased evaded dreamed believed that)
   '(s np vp det n pn vi vt v3)
   's
   (list
    (rule 's '(np vp))
    (rule 'np '(det n))
    (rule 'np '(pn))
    (rule 'det '(a))
    (rule 'det '(the))
    (rule 'n '(mouse))
    (rule 'n '(cat))
    (rule 'n '(dog))
    (rule 'pn '(it))
    (rule 'vp '(vi))
    (rule 'vp '(vt np))
    (rule 'vp '(v3 that s))
    (rule 'vi '(slept))
    (rule 'vi '(swam))
    (rule 'vt '(chased))
    (rule 'vt '(evaded))
    (rule 'v3 '(dreamed))
    (rule 'v3 '(believed)))))

; Here is the grammar for the set of strings consisting of
; n a's followed by n b's, for all nonnegative integers n.

(define grammar-anbn
  (cfg
   '(a b)
   '(s)
   's
   (list
    (rule 's '())
    (rule 's '(a s b)))))

;************************************************************
; A labeled Tree is defined using the following two structs.

(struct node (label children) #:transparent)
(struct leaf (label) #:transparent)

; A labeled Tree is either a leaf with a label
; or a node with a label and a list of labeled Trees as its children.

; Example of a tree.

(define tree1
  (node 'a
        (list
         (node 'b
               (list
                (leaf 'c)
                (leaf 'd)))
         (node 'e
               (list
                (node 'f
                      (list
                       (leaf 'g)
                       (leaf 'h)))
                (leaf 'i))))))

; The procedure (list-leaf-labels tree) returns
; a list of the leaf labels of a labeled Tree.

(define (list-leaf-labels tree)
  (cond
    [(leaf? tree) (list (leaf-label tree))]
    [(node? tree) (append* (map (lambda (x) (list-leaf-labels x)) (node-children tree)))]))

; The procedure (generate-parse-tree-from-cfg grammar)
; takes a CFG grammar and produces a randomly chosen parse Tree from grammar,
; in which all of the node labels are nonterminal symbols and all of
; the leaf labels are terminal symbols.  Every possible such parse tree
; should have a positive probability of being generated, and every other
; parse tree should have probability 0 of being generated.

;determines whether a given symbol symb is the terminal in a grammar
(define (term? symb gram)
  (member symb (cfg-terminals gram)))

;returns a sub-list from a list
(define (s-lst symb lst)
  (cond
    [(null? lst) '()]
    [(equal? symb (rule-lhs (first lst))) (append (list (rule-rhs (first lst))) (s-lst symb (rest lst)))]
    [else (s-lst symb (rest lst))]))

(define (generate-parse-tree-from-cfg grammar)
  (define (generate-tree symbol)
    (if (term? symbol grammar)
        (leaf symbol)
        (node symbol (map (lambda (x) (generate-tree x)) (pick (s-lst symbol (cfg-rules grammar)))))))
  (generate-tree (cfg-start-symbol grammar)))

; The procedure (generate-string-from-cfg grammar)
; takes a CFG grammar and produces a randomly chosen String from grammar.
; Every String in the language of the grammar should have a non-zero
; probability of being generated, and every String not in the language
; should have probability 0 of being generated.

(define (generate-string-from-cfg grammar)
  (define (generate-string symbol)
    (if (term? symbol grammar)
        (list symbol)
        (append* (map (lambda (x) (generate-string x)) (pick (s-lst symbol (cfg-rules grammar)))))))
  (generate-string (cfg-start-symbol grammar)))

; Example: a DFA named dfa-mcd that recognizes the language of 
; the CFG grammar-mcd.

(define dfa-mcd
  (dfa
    '(a the mouse cat dog it slept swam chased evaded dreamed believed that)
    '(q1 q2 q3 q4 q5 q6 q7 q8)
    'q1
    '(q4 q7)
    (list
     (entry '(q1 a) 'q2)
     (entry '(q1 the) 'q2)
     (entry '(q1 it) 'q3)
     (entry '(q2 mouse) 'q3)
     (entry '(q2 cat) 'q3)
     (entry '(q2 dog) 'q3)
     (entry '(q3 slept) 'q4)
     (entry '(q3 swam) 'q4)
     (entry '(q3 chased) 'q5)
     (entry '(q3 evaded) 'q5)
     (entry '(q3 dreamed) 'q8)
     (entry '(q3 believed) 'q8)
     (entry '(q5 a) 'q6)
     (entry '(q5 the) 'q6)
     (entry '(q5 it) 'q7)
     (entry '(q6 mouse) 'q7)
     (entry '(q6 cat) 'q7)
     (entry '(q6 dog) 'q7)
     (entry '(q8 that) 'q1))))

; Example: Regular Expression named exp-mcd that denotes
; the language of the CFG grammar-mcd.

(define exp-mcd
  (concat
   (repeat
    (concat (concat (either (concat (either '(a) '(the)) (either
      (either '(mouse) '(cat)) '(dog))) '(it)) (either '(dreamed) '(believed))) '(that)))
   (concat (either (concat (either '(a) '(the)) (either (either '(mouse) '(cat)) '(dog)))
    '(it)) (either (either '(slept) '(swam)) (concat (either '(chased) '(evaded)) (either
     (concat (either '(a) '(the)) (either (either '(mouse) '(cat)) '(dog))) '(it)))))))

; This context-free grammar parses simple sentences in
; the Punjabi language some example sentences are:

; '(Harman ki karda hai)
; '(satsriakal)
; '(kidda jackie barniec paine sharabi)
; '(Harman Gurpreet Jaspreet Raja)
; '(main tenu baut pyar karda haan)

(define my-cfg
  (cfg
   '(Harman satstriakal kidda main ki tenu karda baut haan karda pyar paine hai sharabi marjaani)
   '(S Ss conj NP VP noun pronoun inter prep)
   'S
   (list
    (rule 'Ss '(conj Ss Ss))
    (rule 'conj '(main))
    (rule 'Ss '(NP VP))
    (rule 'S '(Ss))
    (rule 'S '(inter))
    (rule 'inter '(pyar))
    (rule 'NP '(NP prep NP))
    (rule 'NP '(noun))
    (rule 'NP '(pronoun))
    (rule 'noun '(kidda))
    (rule 'noun '(tenu))
    (rule 'prep '(haan))
    (rule 'pronoun '(Harman))
    (rule 'pronoun '(Gurpreet))
    (rule 'pronoun '(Jaspreet))
    (rule 'pronoun '(Raja)))))

; ********************************************************
; ********  testing, testing. 1, 2, 3 ....
; ********************************************************

(define *testing-flag* #f)
(define error display)

(define (test name got expected)
  (cond (*testing-flag*
	 (let* ((expected (if (procedure? expected)
			      (and (expected got) 'OK-TEST)
			      expected))
		(prefix (if (equal? got expected)
			    '***OK***
			    '---X---)))
	   (list 'testing name prefix 'got: got 'expected: expected)))))
	
(test 'hours hours (lambda (x) (> x 0)))

(test 'ok-string? (ok-string? '()) #t)
(test 'ok-string? (ok-string? '(this is one)) #t)
(test 'ok-string? (ok-string? 'no) #f)
(test 'ok-string? (ok-string? '(0 1)) #f)
(test 'reg-exp? (reg-exp? exp1) #t)
(test 'reg-exp? (reg-exp? exp2) #t)
(test 'reg-exp? (reg-exp? exp3) #t)
(test 'reg-exp? (reg-exp? exp4) #t)
(test 'reg-exp? (reg-exp? 'a) #f)
(test 'reg-exp? (reg-exp? "abbab") #f)
(test 'reg-exp? (reg-exp? '((a b))) #f)

;; NOTE: test results would normally vary due to random elements
;; However, by setting the random-seed, we generate the same sequence of 
;; pseudo random numbers every time.

(random-seed 100)
(test 'flip (flip .5) #f)
(test 'flip (flip .5) #t)
(test 'flip (map (lambda (x) (flip .5)) '(1 2 3 4 5 6 7 8 9 10)) '(#t #f #t #f #f #t #t #f #t #f))
(test 'flip (map (lambda (x) (flip .1)) '(1 2 3 4 5 6 7 8 9 10)) '(#f #f #f #f #f #f #f #f #f #f))
(test 'flip (map (lambda (x) (flip .2)) '(1 2 3 4 5 6 7 8 9 10)) '(#f #f #f #f #f #f #f #f #f #f))
(test 'flip (map (lambda (x) (flip .2)) '(1 2 3 4 5 6 7 8 9 10)) '(#f #t #f #f #f #f #f #f #f #f))

(test 'pick (pick '(1 2 3 4 5 6 8 9 10)) 4)
(test 'pick (pick '(1 2 3 4 5 6 8 9 10)) 3)
(test 'pick (pick '(1 2 3 4 5 6 8 9 10)) 1)
(test 'pick (pick '(1 2 3 4 5 6 8 9 10)) 4)



(test 'generate-string-from-reg-exp (generate-string-from-reg-exp exp1) '())
(test 'generate-string-from-reg-exp (generate-string-from-reg-exp exp2) '(a b b a b))
(test 'generate-string-from-reg-exp (generate-string-from-reg-exp exp3) '(a b d))
(test 'generate-string-from-reg-exp (generate-string-from-reg-exp exp4) '(b b a))
(test 'generate-string-from-reg-exp (generate-string-from-reg-exp exp4) '(b))
(test 'generate-string-from-reg-exp (generate-string-from-reg-exp exp5) '(the cat ran))

(test 'dfa-accepts? (dfa-accepts? even-as '(a b b a b)) #t)
(test 'dfa-accepts? (dfa-accepts? even-as '(b b a b b b)) #f)
(test 'dfa-accepts? (dfa-accepts? car-cdr '(c a d a r)) #t)
(test 'dfa-accepts? (dfa-accepts? car-cdr '(c a r d)) #f)

(test 'list-leaf-labels (list-leaf-labels tree1) '(c d g h i))

(test 'generate-parse-tree-from-cfg (generate-parse-tree-from-cfg grammar-mcd)
 (node
  's
  (list
   (node 'np (list (node 'pn (list (leaf 'it)))))
   (node 'vp (list (node 'vi (list (leaf 'swam))))))))

(test 'generate-string-from-cfg (generate-string-from-cfg grammar-mcd) '(a cat evaded it))
(test 'generate-string-from-cfg (generate-string-from-cfg grammar-anbn) '(a a a b b b))
(test 'generate-string-from-cfg (generate-string-from-cfg grammar-anbn) '(a a a b b b))
(test 'generate-string-from-cfg (generate-string-from-cfg grammar-anbn) '(a a b b))
