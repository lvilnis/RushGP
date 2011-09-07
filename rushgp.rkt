#|
rushgp.rkt 

This file implements a version of the Push programming language (http://hampshire.edu/lspector/push.html) 
and the PushGP genetic programming system in Typed Racket (http://racket-lang.org/).

LICENSE:

Copyright (c) 2011 Luke Vilnis

This work is based on (versions as of 8/21/2011):

Schush/SchushGP (http://hampshire.edu/lspector/schush.ss), copyright (c) 2009, 2010 Lee Spector 
Clojush/ClojushGP (https://github.com/lspector/Clojush), copyright (c) 2010, 2011 Lee Spector

both distributed under version 3 of the GNU General Public License as published by the
Free Software Foundation, available from http://www.gnu.org/licenses/gpl.txt.

This program is free software: you can redistribute it and/or modify it under
the terms of version 3 of the GNU General Public License as published by the
Free Software Foundation, available from http://www.gnu.org/licenses/gpl.txt.

This program is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE. See the GNU General Public License (http://www.gnu.org/licenses/)
for more details.

HOW TO USE:

Look at the example1, example2, or example3 functions at the end of the source for a demonstration
of how to use this implementation of PushGP.

HISTORY:

8/10/2011: Started work.
8/21/2011: First version released.
9/5/2011: Cleaned up some instruction definitions, added some annotations and helpers to get RushGP building in Racket 5.1.3.
9/6/2011: Made sure RushGP builds in both Racket 5.1.2 and 5.1.3 for comparison, small type-based optimizations.
|#

#lang typed/racket

;; Push types

(define-type 
  PushType 
  (U 'exec 'integer 'float 'code 'boolean 'auxiliary 'tag 'zip))

(define-type Instruction Symbol)

(define-type
  Literal
  (U Integer Float Boolean))

(define-type
  Program
  (Rec Prog (U Instruction Literal (Listof Prog))))

(define-type (Stack a) (Listof a))

(struct: 
  ProgramState
  ([Exec : (Stack Program)]
   [Integer : (Stack Integer)]
   [Float : (Stack Float)]
   [Code : (Stack Program)]
   [Boolean : (Stack Boolean)]
   [Auxiliary : (Stack Program)]
   [Tag : (Stack Program)]
   [Zip : (Stack Program)]))

(struct:
  Instruction-Definition
  ([Type : PushType]
   [Name : Symbol]
   [Definition : (ProgramState -> ProgramState)]))

(define-predicate PushType? PushType)
(define-predicate Literal? Literal)
(define-predicate Boolean? Boolean)
(define-predicate Float? Float)
(define-predicate Integer? Integer)
(define-predicate Program-Sequence? (Listof Program))
(define-predicate Program? Program)
(define-predicate Instruction? Instruction)
(define-predicate Exact-Positive-Integer? Exact-Positive-Integer)
 
;; pushgp parameters

(: max-number-magnitude Integer)
(define max-number-magnitude 1000000000000)

(: min-number-magnitude Float)
(define min-number-magnitude 1.0E-10)

(: top-level-push-code Boolean)
(define top-level-push-code #t)

(: top-level-pop-code Boolean)
(define top-level-pop-code #f)

(: evalpush-limit Integer)
(define evalpush-limit 150)

(: save-traces Boolean)
(define save-traces #t)

;; utilities

(define-syntax pλ:
  (syntax-rules ()
    ((_ args ...)
     (plambda: args ...))))

(: real->float ((U Real Inexact-Real) -> Float))
(define (real->float ir)
  (match (exact->inexact ir)
    [(? Float? flt) flt]
    [_ (error "Inexact real isn't float?")]))

(: sum-floats ((Listof Float) -> Float))
(define (sum-floats flts)
  (foldl (λ: ([el : Float] [acc : Float]) (+ el acc)) (ann 0.0 Float) flts))

(: rand-int (Integer -> Integer))
(define (rand-int seed)
  (cond
    [(>= seed 1) (random seed)]
    [else 0]))

(: copy-tree (Program -> Program))
(define (copy-tree tree)
  (match tree
    ['() '()]
    [(? Program-Sequence? ps) (apply map copy-tree ps '())]
    [_ tree]))

(: keep-number-reasonable (Float -> Float))
(define (keep-number-reasonable flt) 
  (cond [(> flt max-number-magnitude) (exact->inexact max-number-magnitude)]
        [(< flt (- max-number-magnitude)) (exact->inexact (- max-number-magnitude))]
        [(and (< flt min-number-magnitude)
              (> flt (- min-number-magnitude)))
         (ann 0.0 Float)]
        [else flt]))

(: count-points (Program -> Integer))
(define (count-points prog)
  (match prog
    [(? Program-Sequence? ps) (+ 1 (apply + (map count-points ps)))]
    [_ 1]))

(: code-at-point-recursive (Program Integer Integer -> Program))
(define (code-at-point-recursive tree point-index points-so-far)
  (match point-index
    [0 tree]
    [_ (match tree
         ['() '()]
         [(cons first-subtree rest)
          (define points-in-first-subtree (count-points first-subtree))
          (define new-points-so-far (+ points-so-far points-in-first-subtree))
          (if (<= point-index new-points-so-far)
              (code-at-point-recursive first-subtree (- point-index points-so-far 1) 0)
              (code-at-point-recursive rest point-index new-points-so-far))]
         [_ tree])]))

(: code-at-point (Program Integer -> Program))
(define (code-at-point tree point-index)
  (code-at-point-recursive 
   tree
   (abs (modulo (abs point-index) (max 1 (count-points tree))))
   0))

(: trunc (Float -> Integer))
(define (trunc n)
  (ann (truncate (inexact->exact n)) Integer))

(: insert-code-at-point-recursive (Program Program Integer Integer -> Program))
(define (insert-code-at-point-recursive tree new-subtree point-index points-so-far)
  (match point-index
    [0 new-subtree]
    [_ (match tree
         ['() '()]
         [(cons first-subtree rest)
          (define points-in-first-subtree (count-points first-subtree))
          (define new-points-so-far (+ points-so-far points-in-first-subtree))
          (if (<= point-index new-points-so-far)
              (cons (insert-code-at-point-recursive first-subtree new-subtree (- point-index points-so-far 1) 0) rest)
              (cons first-subtree
                    (match (insert-code-at-point-recursive rest new-subtree point-index new-points-so-far)
                      [(? Program-Sequence? replaced-rest) replaced-rest]
                      [_ '()])))]
         [_ new-subtree])]))

(: insert-code-at-point (Program Integer Program -> Program))
(define (insert-code-at-point tree point-index new-subtree)
  (insert-code-at-point-recursive tree
                                  new-subtree
                                  (abs (modulo (abs point-index) (count-points tree)))
                                  0))

(: remove-code-at-point (Program Integer -> Program))
(define (remove-code-at-point tree point-index)
  (define normed-point-index (abs (modulo point-index (count-points tree))))
  (: remove-sillymarker24 (Program -> Program))
  (define (remove-sillymarker24 prog)
    (match prog
      [(? Program-Sequence? ps)
       (define no-marker (filter (λ: ([p : Program]) 
                                   (match p
                                     ['sillymarker24 false]
                                     [_ true])) ps))
       ((inst map Program Program) remove-sillymarker24 no-marker)]
      [_ prog])) 
  (match* (tree point-index)
    [('() _) '()] 
    [(_ 0) '()]
    [(_ _)
     (remove-sillymarker24
      (insert-code-at-point-recursive tree 'sillymarker24 point-index 0))]))

(: prog->string (Program -> String))
(define (prog->string prog) 
  (match prog
    [(? Program-Sequence? ps) (string-append "(" (string-join (map prog->string ps) " ") ")")]
    [(? Instruction? instr) (string-downcase (symbol->string instr))]
    [lit (format "~A" lit)]))

(: state-pretty-print (ProgramState -> Void))
(define (state-pretty-print state)
  (printf "- Exec: ~A~%" (map prog->string (ProgramState-Exec state)))
  (printf "- Integer: ~A~%" (ProgramState-Integer state))
  (printf "- Float: ~A~%" (ProgramState-Float state))
  (printf "- Code: ~A~%" (map prog->string (ProgramState-Code state)))
  (printf "- Boolean: ~A~%" (ProgramState-Boolean state))
  (printf "- Auxiliary: ~A~%" (ProgramState-Auxiliary state))
  (printf "- Tag: ~A~%" (ProgramState-Tag state))
  (printf "- Zip: ~A~%" (ProgramState-Zip state)))

(: flatten-program (Program -> Program))
(define (flatten-program prog)
  (match prog
    [(? Program-Sequence? ps)
     (apply append (map (compose ensure-list flatten-program) ps))]
    [_ prog]))

(: repeat (All (a) (a Integer -> (Listof a))))
(define (repeat item num-times)
  (match num-times
    [1 `(,item)]
    [_ (cons item (repeat item (- num-times 1)))]))

;; Macros and functions for registering push instructions and related fancy business

(: instructions (Listof Instruction-Definition))
(define instructions '())

(: instruction-table (HashTable String (ProgramState -> ProgramState)))
(define instruction-table (make-hash))

(: definition->instr (Instruction-Definition -> Instruction))
(define (definition->instr id)
  (string->symbol (format "~A.~A" (Instruction-Definition-Type id) (Instruction-Definition-Name id))))

(: definition->string (Instruction-Definition -> String))
(define (definition->string id)
  (string-downcase (symbol->string (definition->instr id))))

(: make-instr (PushType Symbol -> Instruction))
(define (make-instr type name)
  (string->symbol (string-downcase (format "~A.~A" type name))))

(: register (Instruction-Definition (ProgramState -> ProgramState) -> Void))
(define (register instruction definition)
  (set! instructions (cons instruction instructions))
  ((inst hash-set! String (ProgramState -> ProgramState)) instruction-table (definition->string instruction) definition))

(: registered-for-type (PushType -> (Listof Instruction)))
(define (registered-for-type pt)
  (map (λ: ([id : Instruction-Definition]) (definition->instr id))
       (filter (λ: ([id : Instruction-Definition]) (equal? pt (Instruction-Definition-Type id)))
               instructions)))

(define-syntax define-instruction
  (syntax-rules ()
    ((_ type instruction definition)
     (register (Instruction-Definition 'type 'instruction definition) definition))))

(define-syntax with-stacks
  (syntax-rules ()
    ((_ ps args ...)
     (struct-copy ProgramState ps args ...))))

(: get-stack-inst-list (Symbol (All (a) ((Stack a) -> (Stack a))) -> (Listof Instruction-Definition)))
(define (get-stack-inst-list sym definition) 
  (list 
   (Instruction-Definition 'exec sym (λ (ps) (with-stacks ps [Exec (definition (ProgramState-Exec ps))])))
   (Instruction-Definition 'integer sym (λ (ps) (with-stacks ps [Integer (definition (ProgramState-Integer ps))])))
   (Instruction-Definition 'float sym (λ (ps) (with-stacks ps [Float (definition (ProgramState-Float ps))])))
   (Instruction-Definition 'code sym (λ (ps) (with-stacks ps [Code (definition (ProgramState-Code ps))])))
   (Instruction-Definition 'boolean sym (λ (ps) (with-stacks ps [Boolean (definition (ProgramState-Boolean ps))])))))


(: define-stack-instructions-function (Symbol (All (a) ((Stack a) -> (Stack a))) -> Void))
(define (define-stack-instructions-function sym definition)
  (for ((instr (get-stack-inst-list sym definition)))
    (set! instructions (cons instr instructions))
    ((inst hash-set! String (ProgramState -> ProgramState)) instruction-table (definition->string instr) (Instruction-Definition-Definition instr))))

(define-syntax define-stack-instructions
  (syntax-rules ()
    ((_ instruction definition)
     (define-stack-instructions-function 'instruction definition))))

(: get-inst-list (Symbol (All (a) (ProgramState -> (Stack a)) (ProgramState (Stack a) -> ProgramState) -> (ProgramState -> ProgramState)) -> (Listof Instruction-Definition)))
(define (get-inst-list sym definition)  
  (list 
   (Instruction-Definition 'exec sym 
                           ((inst definition Program) (λ: ([ps : ProgramState]) (ProgramState-Exec ps)) 
                                                      (λ: ([ps : ProgramState] [stk : (Stack Program)]) (with-stacks ps [Exec stk]))))
   (Instruction-Definition 'integer sym
                           ((inst definition Integer) (λ: ([ps : ProgramState]) (ProgramState-Integer ps)) 
                                                      (λ: ([ps : ProgramState] [stk : (Stack Integer)]) (with-stacks ps [Integer stk]))))
   (Instruction-Definition 'float sym
                           ((inst definition Float) (λ: ([ps : ProgramState]) (ProgramState-Float ps)) 
                                                    (λ: ([ps : ProgramState] [stk : (Stack Float)]) (with-stacks ps [Float stk]))))
   (Instruction-Definition 'code sym
                           ((inst definition Program) (λ: ([ps : ProgramState]) (ProgramState-Code ps)) 
                                                      (λ: ([ps : ProgramState] [stk : (Stack Program)]) (with-stacks ps [Code stk]))))
   (Instruction-Definition 'boolean sym
                           ((inst definition Boolean) (λ: ([ps : ProgramState]) (ProgramState-Boolean ps)) 
                                                      (λ: ([ps : ProgramState] [stk : (Stack Boolean)]) (with-stacks ps [Boolean stk]))))))

(: define-instructions-function (Symbol (All (a) (ProgramState -> (Stack a)) (ProgramState (Stack a) -> ProgramState) -> (ProgramState -> ProgramState)) -> Void))
(define (define-instructions-function sym definition)
  (for ((instr (get-inst-list sym definition))) 
    (set! instructions (cons instr instructions))
    ((inst hash-set! String (ProgramState -> ProgramState)) instruction-table (definition->string instr) (Instruction-Definition-Definition instr))))

(define-syntax define-instructions
  (syntax-rules ()
    ((_ instruction definition)
     (define-instructions-function 'instruction definition))))

;; Integer and float instructions

(: int-binop ((Integer Integer -> Integer) -> (ProgramState -> ProgramState)))
(define ((int-binop op) ps) 
  (match (ProgramState-Integer ps)
    [(list-rest a b rest) (with-stacks ps [Integer (cons (op a b) rest)])]
    [_ ps]))

(: float-binop ((Float Float -> Float) -> (ProgramState -> ProgramState)))
(define ((float-binop op) ps) 
  (match (ProgramState-Float ps)
    [(list-rest a b rest) (with-stacks ps [Float (cons (op a b) rest)])]
    [_ ps]))

(: float-unop ((Float -> Float) -> (ProgramState -> ProgramState)))
(define ((float-unop op) ps) 
  (match (ProgramState-Float ps) 
    [(cons a rest) (with-stacks ps [Float (cons (op a) rest)])]
    [_ ps]))

(define-instruction integer ADD (int-binop +))
(define-instruction float ADD (float-binop +))

(define-instruction integer SUB (int-binop -))
(define-instruction float SUB (float-binop -))

(define-instruction integer MULT (int-binop *))
(define-instruction float MULT (float-binop *))

(define-instruction integer MIN (int-binop min))
(define-instruction float MIN (float-binop min))

(define-instruction integer MAX (int-binop max))
(define-instruction float MAX (float-binop max))

(define-instruction integer MOD (int-binop (λ: ([a : Integer] [b : Integer]) (modulo a (max 1 b)))))

(define-instruction float DIV (float-binop /))

(define-instruction float SIN (float-unop sin))
(define-instruction float COS (float-unop cos))
(define-instruction float TAN (float-unop tan))

(define-instruction float < 
  (λ: ([ps : ProgramState])
    (match (ProgramState-Float ps)
      [(list-rest a b rest)
       (with-stacks ps [Float rest] [Boolean (cons (< a b) (ProgramState-Boolean ps))])]
      [_ ps])))

(define-instruction integer < 
  (λ: ([ps : ProgramState])
    (match (ProgramState-Integer ps)
      [(list-rest a b rest)
       (with-stacks ps [Integer rest] [Boolean (cons (< a b) (ProgramState-Boolean ps))])]
      [_ ps])))

(define-instruction float > 
  (λ: ([ps : ProgramState])
    (match (ProgramState-Float ps)
      [(list-rest a b rest)
       (with-stacks ps [Float rest] [Boolean (cons (> a b) (ProgramState-Boolean ps))])]
      [_ ps])))

(define-instruction integer > 
  (λ: ([ps : ProgramState])
    (match (ProgramState-Integer ps)
      [(list-rest a b rest)
       (with-stacks ps [Integer rest] [Boolean (cons (> a b) (ProgramState-Boolean ps))])]
      [_ ps])))

(define-instruction float FROMBOOLEAN 
  (λ: ([ps : ProgramState])
    (match (ProgramState-Boolean ps)
      [(list-rest a rest)
       (define flt (if a 1.0 (ann 0.0 Float)))
       (with-stacks ps [Float (cons flt (ProgramState-Float ps))] [Boolean rest])]
      [_ ps])))

(define-instruction integer FROMBOOLEAN 
  (λ: ([ps : ProgramState])
    (match (ProgramState-Boolean ps)
      [(cons a rest)
       (define int (if a 1 0))
       (with-stacks ps [Integer (cons int (ProgramState-Integer ps))] [Boolean rest])]
      [_ ps])))

(define-instruction float FROMINTEGER
  (λ: ([ps : ProgramState])
    (match (ProgramState-Integer ps)
      [(cons int rest)
       (define flt (ann (exact->inexact int) Float))
       (with-stacks ps [Float (cons flt (ProgramState-Float ps))] [Integer rest])]
      [_ ps])))

(define-instruction integer FROMFLOAT
  (λ: ([ps : ProgramState])
    (match (ProgramState-Float ps)
      [(cons flt rest)
       (define int (trunc flt))
       (with-stacks ps [Integer (cons int (ProgramState-Integer ps))] [Float rest])]
      [_ ps])))

;; Boolean instructions

(: bool-binop ((Boolean Boolean -> Boolean) -> (ProgramState -> ProgramState)))
(define ((bool-binop op) ps) 
  (match (ProgramState-Boolean ps)
    [`(,a ,b . ,rest) (with-stacks ps [Boolean (cons (op a b) rest)])]
    [_ ps]))

(: bool-unop ((Boolean -> Boolean) -> (ProgramState -> ProgramState)))
(define ((bool-unop op) ps) 
  (match (ProgramState-Boolean ps)
    [(cons a rest) (with-stacks ps [Boolean (cons (op a) rest)])]
    [_ ps]))

(define-instruction boolean AND (bool-binop (λ: ([a : Boolean] [b : Boolean]) (and a b))))
(define-instruction boolean OR (bool-binop (λ: ([a : Boolean] [b : Boolean]) (or a b))))
(define-instruction boolean NOT (bool-unop (λ: ([a : Boolean]) (not a))))

(define-instruction boolean FROMFLOAT 
  (λ: ([ps : ProgramState])
    (match (ProgramState-Float ps)
      [(cons flt rest)
       (define bool (= 0.0 flt))
       (with-stacks ps [Boolean (cons bool (ProgramState-Boolean ps))] [Float rest])]
      [_ ps])))

(define-instruction boolean FROMINTEGER
  (λ: ([ps : ProgramState])
    (match (ProgramState-Integer ps)
      [(cons int rest)
       (define bool (= 0 int))
       (with-stacks ps [Boolean (cons bool (ProgramState-Boolean ps))] [Integer rest])]
      [_ ps])))

;; Code and exec instructions

(: ensure-list (Program -> (Listof Program)))
(define (ensure-list thing)
  (match thing
    [(? Program-Sequence? thing) thing]
    [_ `(,thing)]))

(define-instruction code APPEND
  (λ: ([ps : ProgramState])
    (match (ProgramState-Code ps)
      [`(,a ,b . ,rest)
       (with-stacks ps [Code (cons (append (ensure-list a) (ensure-list b)) rest)])]
      [_ ps])))

(define-instruction code ATOM
  (λ: ([ps : ProgramState])
    (match (ProgramState-Code ps)
      [(cons a rest)
       (with-stacks ps [Code (cons (not (pair? a)) rest)])]
      [_ ps])))

(define-instruction code CAR
  (λ: ([ps : ProgramState])
    (match (ProgramState-Code ps)
      [`((,hd . ,tl) . ,rest)
       (with-stacks ps [Code (cons hd rest)])]
      [_ ps])))

(define-instruction code CDR
  (λ: ([ps : ProgramState])
    (match (ProgramState-Code ps)
      [(cons (app ensure-list (cons hd tl)) rest)
       (with-stacks ps [Code (cons tl rest)])]
      [_ ps])))

(define-instruction code CONS
  (λ: ([ps : ProgramState])
    (match (ProgramState-Code ps)
      [`(,(app ensure-list top-item) ,second-item . ,rest)
       (with-stacks ps [Code (cons (cons second-item top-item) rest)])]
      [_ ps])))

(define-instruction code DO
  (λ: ([ps : ProgramState])
    (match (ProgramState-Code ps)
      [(cons prog rest)
       (with-stacks ps [Exec `(,prog code.pop . ,(ProgramState-Exec ps))])]
      [_ ps])))

(define-instruction code DO*
  (λ: ([ps : ProgramState])
    (match (ProgramState-Code ps)
      [(cons prog rest)
       (with-stacks ps [Code rest] [Exec (cons prog (ProgramState-Exec ps))])]
      [_ ps])))

(define-instruction code DO*RANGE
  (λ: ([ps : ProgramState])
    (match* ((ProgramState-Code ps) (ProgramState-Integer ps))
      [((cons to-do code-rest) `(,destination-index ,current-index . ,int-rest))
       (define increment 
         (cond [(< current-index destination-index) 1]
               [(> current-index destination-index) -1]
               [else 0]))
       (define new-state (with-stacks ps [Integer (cons current-index int-rest)] [Code code-rest]))
       (define new-instruction
         (match increment
           [0 (copy-tree to-do)]
           [_ 
            (list (+ current-index increment)
                  destination-index
                  'code.quote
                  (copy-tree to-do)
                  'code.do*range)]))
       (with-stacks new-state [Exec (cons new-instruction (ProgramState-Exec new-state))])]
      [(_ _) ps])))

(define-instruction exec DO*RANGE
  (λ: ([ps : ProgramState])
    (match* ((ProgramState-Exec ps) (ProgramState-Integer ps))
      [((cons to-do code-rest) (list-rest destination-index current-index int-rest))
       (define increment 
         (cond [(< current-index destination-index) 1]
               [(> current-index destination-index) -1]
               [else 0]))
       (define new-state (with-stacks ps [Integer (cons current-index int-rest)] [Exec code-rest]))
       (define new-instruction
         (match increment
           [0 (copy-tree to-do)]
           [_ 
            (list (+ current-index increment)
                  destination-index
                  'exec.do*range
                  (copy-tree to-do))]))
       (with-stacks new-state [Exec (cons new-instruction (ProgramState-Exec new-state))])]
      [(_ _) ps])))

(define-instruction code DO*COUNT
  (λ: ([ps : ProgramState])
    (match (ProgramState-Code ps)
      [(cons to-do code-rest)
       (match (ProgramState-Integer ps)
         [(cons 0 int-rest) ps]
         [(cons num-times int-rest)
          (define new-instruction 
            (list 0 (- num-times 1) 'code.quote (copy-tree to-do) 'code.do*range))
          (with-stacks ps [Exec (cons new-instruction (ProgramState-Exec ps))] [Code code-rest] [Integer int-rest])]
         [_ ps])]
      [_ ps])))

(define-instruction exec DO*COUNT
  (λ: ([ps : ProgramState])
    (match (ProgramState-Exec ps)
      [(cons to-do exec-rest)
       (match (ProgramState-Integer ps)
         [(cons 0 int-rest) ps]
         [(cons num-times int-rest)
          (define new-instruction 
            (list 0 (- num-times 1) 'exec.do*range (copy-tree to-do)))
          (with-stacks ps [Exec (cons new-instruction exec-rest)] [Integer int-rest])]
         [_ ps])]
      [_ ps])))

(define-instruction code DO*TIMES
  (λ: ([ps : ProgramState])
    (match (ProgramState-Code ps)
      [(cons to-do code-rest)
       (match (ProgramState-Integer ps)
         [(cons 0 int-rest) ps]
         [(cons num-times int-rest)
          (define new-instruction 
            (list 0 
                  (- num-times 1) 
                  'code.quote
                  (cons 'integer.pop (ensure-list (copy-tree to-do))) 
                  'code.do*range))
          (with-stacks ps [Exec (cons new-instruction (ProgramState-Exec ps))] [Code code-rest] [Integer int-rest])]
         [_ ps])]
      [_ ps])))

(define-instruction exec DO*TIMES
  (λ: ([ps : ProgramState])
    (match (ProgramState-Exec ps)
      [(cons to-do exec-rest)
       (match (ProgramState-Integer ps)
         [(cons 0 int-rest) ps]
         [(cons num-times int-rest)
          (define new-instruction 
            (list 0 
                  (- num-times 1) 
                  'exec.do*range 
                  (cons 'integer.pop (ensure-list (copy-tree to-do)))))
          (with-stacks ps [Exec (cons new-instruction exec-rest)] [Integer int-rest])]
         [_ ps])]
      [_ ps])))

(define-instruction code FROMBOOLEAN
  (λ: ([ps : ProgramState])
    (match (ProgramState-Boolean ps)
      [(cons hd tl)
       (with-stacks ps [Code (cons hd (ProgramState-Code ps))] [Boolean tl])]
      [_ ps])))

(define-instruction code FROMINTEGER
  (λ: ([ps : ProgramState])
    (match (ProgramState-Integer ps)
      [(cons hd tl)
       (with-stacks ps [Code (cons hd (ProgramState-Code ps))] [Integer tl])]
      [_ ps])))

(define-instruction code FROMFLOAT
  (λ: ([ps : ProgramState])
    (match (ProgramState-Float ps)
      [(cons hd tl)
       (with-stacks ps [Code (cons hd (ProgramState-Code ps))] [Float tl])]
      [_ ps])))

(define-instruction code QUOTE
  (λ: ([ps : ProgramState])
    (match (ProgramState-Exec ps)
      [(cons hd tl)
       (with-stacks ps [Code (cons hd (ProgramState-Code ps))] [Exec tl])]
      [_ ps])))

(define-instruction code IF
  (λ: ([ps : ProgramState])
    (match* ((ProgramState-Code ps) (ProgramState-Boolean ps))
      [((list-rest fst snd code-rest) (cons cond bool-rest))
       (define to-do (if cond fst snd))
       (with-stacks ps [Exec (cons (copy-tree to-do) (ProgramState-Exec ps))] [Boolean bool-rest] [Code code-rest])]
      [(_ _) ps])))

(define-instruction exec IF
  (λ: ([ps : ProgramState])
    (match* ((ProgramState-Exec ps) (ProgramState-Boolean ps))
      [(`(,fst ,snd . ,exec-rest) (cons cond bool-rest))
       (define to-do (if cond snd fst))
       (with-stacks ps [Exec (cons (copy-tree to-do) exec-rest)] [Boolean bool-rest])]
      [(_ _) ps])))

(define-instruction code LENGTH
  (λ: ([ps : ProgramState])
    (match (ProgramState-Code ps)
      [(cons (app ensure-list first-code) code-rest)
       (with-stacks ps [Integer (cons (length first-code) (ProgramState-Integer ps))] [Code code-rest])]
      [_ ps])))

(define-instruction code LIST
  (λ: ([ps : ProgramState])
    (match (ProgramState-Code ps)
      [(list-rest top-item second-item code-rest)
       (with-stacks ps [Code `((,second-item ,top-item) . ,code-rest)])]
      [_ ps])))

(define-instruction code NOOP (λ (ps) ps))
(define-instruction exec NOOP (λ (ps) ps))

(define-instruction code MEMBER
  (λ: ([ps : ProgramState]) 
    (match (ProgramState-Code ps)
      [`(,top-item ,second-item . ,code-rest)
       (define new-bool-stack
         (cons (not (not (member second-item (ensure-list top-item)))) (ProgramState-Boolean ps)))
       (with-stacks ps [Boolean new-bool-stack] [Code code-rest])]
      [_ ps])))

(define-instruction code NTH
  (λ: ([ps : ProgramState]) 
    (match* ((ProgramState-Code ps) (ProgramState-Integer ps))
      [((cons (app ensure-list (and the-list (cons _ _))) code-rest) (cons n int-rest))
       (define new-item (list-ref the-list (modulo (abs n) (length the-list))))
       (with-stacks ps [Integer int-rest] [Code (cons new-item code-rest)])]
      [(_ _) ps])))

(define-instruction code NTHCDR
  (λ: ([ps : ProgramState]) 
    (match* ((ProgramState-Code ps) (ProgramState-Integer ps))
      [((cons (app ensure-list (and the-list (cons _ _))) code-rest) (cons n int-rest))
       (define new-item (list-tail the-list (modulo (abs n) (length the-list))))
       (with-stacks ps [Integer int-rest] [Code (cons new-item code-rest)])]
      [(_ _) ps])))

(define-instruction code NULL
  (λ: ([ps : ProgramState]) 
    (match (ProgramState-Code ps)
      [(cons item code-rest)
       (with-stacks ps [Boolean (cons (null? item) (ProgramState-Boolean ps))] [Code code-rest])]
      [_ ps])))

(define-instruction code SIZE
  (λ: ([ps : ProgramState]) 
    (match (ProgramState-Code ps)
      [(cons item code-rest)
       (with-stacks ps [Integer (cons (count-points item) (ProgramState-Integer ps))] [Code code-rest])]
      [_ ps])))

(define-instruction exec K
  (λ: ([ps : ProgramState]) 
    (match (ProgramState-Exec ps)
      [(list-rest x _ exec-rest)
       (with-stacks ps [Exec (cons x exec-rest)])]
      [_ ps])))

(define-instruction exec S
  (λ: ([ps : ProgramState]) 
    (match (ProgramState-Exec ps)
      [(list-rest x y z exec-rest)
       (define new-exec (append `(,x ,z (,y ,z)) exec-rest))
       (with-stacks ps [Exec new-exec])]
      [_ ps])))

(define-instruction exec Y
  (λ: ([ps : ProgramState]) 
    (match (ProgramState-Exec ps)
      [(cons x exec-rest)
       (define new-exec `(,x exec.y . ,exec-rest))
       (with-stacks ps [Exec new-exec])]
      [_ ps])))

;; Instructions for all types

(define-stack-instructions DUP 
  (pλ: (a) ([stack : (Stack a)]) 
    (match stack 
      [(cons hd tl) `(,hd ,hd . ,tl)]
      [_ stack])))

(define-stack-instructions POP 
  (pλ: (a) ([stack : (Stack a)]) 
    (match stack 
      [(cons hd tl) tl]
      [_ stack])))

(define-stack-instructions SWAP 
  (pλ: (a) ([stack : (Stack a)]) 
    (match stack 
      [`(,a ,b . ,tl) `(,b ,a . ,tl)]
      [_ stack])))

(define-stack-instructions ROT 
  (pλ: (a) ([stack : (Stack a)]) 
    (match stack 
      [`(,a ,b ,c . ,tl) `(,c ,a ,b . ,tl)]
      [_ stack])))

(define-stack-instructions FLUSH 
  (pλ: (a) ([stack : (Stack a)]) 
    '()))

(: id (All (a) (a -> a)))
(define (id x) x)

(define-instructions EQUAL 
  (pλ: (a) ([get-stack : (ProgramState -> (Stack a))] 
            [set-stack : (ProgramState (Stack a) -> ProgramState)])
    (λ: ([ps : ProgramState]) 
      (match (get-stack ps)
        [(list-rest a b rest) 
         (define new-state (set-stack ps rest))
         (define new-bool-stack (cons (equal? a b) (ProgramState-Boolean new-state)))
         (with-stacks new-state [Boolean new-bool-stack])]
        [_ ps]))))

(define-instructions STACKDEPTH 
  (pλ: (a) ([get-stack : (ProgramState -> (Stack a))] 
            [set-stack : (ProgramState (Stack a) -> ProgramState)])
    (λ: ([ps : ProgramState]) 
      (define stack-depth (length (get-stack ps)))
      (with-stacks ps [Integer (cons stack-depth (ProgramState-Integer ps))]))))

(define-instructions YANK 
  (pλ: (a) ([get-stack : (ProgramState -> (Stack a))] 
            [set-stack : (ProgramState (Stack a) -> ProgramState)])
    (λ: ([ps : ProgramState]) 
      (match (ProgramState-Integer ps)
        ['() ps]
        [(cons raw-yank-index rest)
         (define new-state (with-stacks ps [Integer rest]))
         (match (get-stack new-state)
           ['() ps]
           [stk 
            (define yank-index (max 0 (min raw-yank-index (- (length stk) 1))))
            (define item (list-ref stk yank-index))
            (define stk-without-item (append (take stk yank-index) (drop stk (+ yank-index 1))))
            (set-stack new-state (cons item stk-without-item))])]))))

(define-instructions YANKDUP 
  (pλ: (a) ([get-stack : (ProgramState -> (Stack a))] 
            [set-stack : (ProgramState (Stack a) -> ProgramState)])
    (λ: ([ps : ProgramState]) 
      (match (ProgramState-Integer ps)
        ['() ps]
        [(cons raw-yank-index rest)
         (define new-state (with-stacks ps [Integer rest]))
         (match (get-stack new-state)
           ['() ps]
           [stk 
            (define yank-index (max 0 (min raw-yank-index (- (length stk) 1))))
            (define item (list-ref stk yank-index))
            (set-stack new-state (cons item stk))])]))))

;; Random code generation

(define-type Atom-Generator (U (-> Program) Program))

(: random-element (All (a) ((Listof a) -> a)))
(define (random-element xs)
  (list-ref xs (rand-int (length xs))))

(: shuffle (All (a) ((Listof a) -> (Listof a))))
(define (shuffle xs)
  (match xs
    [(cons _ _) 
     (define item (random-element xs))
     (cons item (shuffle (remove item xs)))]
    [_ xs]))

(: decompose (Integer Integer -> (Listof Integer)))
(define (decompose number max-parts) 
  (cond
    [(or (<= max-parts 1) (<= number 1)) 
     `(,number)]
    [else
     (define this-part (+ 1 (rand-int (- number 1))))
     (cons this-part (decompose (- number this-part) (- max-parts 1)))]))

(: random-code-with-size (Integer (Listof Atom-Generator) -> Program))
(define (random-code-with-size points atom-generators)  
  (cond 
    [(< points 2)
     (define element (random-element atom-generators))
     (if (Program? element) element (element))]
    [else 
     (define elements-this-level (shuffle (decompose (- points 1) (- points 1))))
     (ann ((inst map Program Integer) (λ: ([size : Integer]) (random-code-with-size size atom-generators)) elements-this-level) Program)]))

(: random-code (Integer (Listof Atom-Generator) -> Program))
(define (random-code max-points atom-generators) 
  (random-code-with-size (+ 1 (rand-int max-points)) atom-generators))

;; Interpreter

;; all these push-foo routines feel pretty ugly... should I use a macro and parametrize with PushType?

(: push-integer (Integer ProgramState -> ProgramState))
(define (push-integer int ps)
  (with-stacks ps [Integer (cons int (ProgramState-Integer ps))]))

(: push-float (Float ProgramState -> ProgramState))
(define (push-float flt ps)
  (with-stacks ps [Float (cons flt (ProgramState-Float ps))]))

(: push-boolean (Boolean ProgramState -> ProgramState))
(define (push-boolean bool ps)
  (with-stacks ps [Boolean (cons bool (ProgramState-Boolean ps))]))

(: push-code (Program ProgramState -> ProgramState))
(define (push-code code ps)
  (with-stacks ps [Code (cons code (ProgramState-Code ps))]))

(: push-exec (Program ProgramState -> ProgramState))
(define (push-exec code ps)
  (with-stacks ps [Exec (cons code (ProgramState-Exec ps))]))

(: lookup-instruction (Instruction -> (ProgramState -> ProgramState)))
(define (lookup-instruction instr)
  ;;(printf "Executing instruction: ~A" instr)
  (hash-ref instruction-table (string-downcase (symbol->string instr))))

;; something is messed up with 0.0
;; i had the following Program-Sequence fail to match: '(0 9 code.quote 0.0 code.do*range)
;; somehow i'm getting 0.0 not matching the Instruction predicate at some point, even though if I
;; type it out by hand (e.g. (Instruction? 0.0) and the like), it seems to work fine

(: execute (ProgramState Integer (Listof Program) Boolean -> ProgramState))
(define (execute current-state execution-count traces print)
  (match (ProgramState-Exec current-state)
    ['() current-state]
    [(cons exec-top new-exec)
     (define next-state 
       (match exec-top
         [(? Instruction? instr)
          (with-handlers 
              ([(λ (_) #t) 
                (λ (a) 
                  (printf "Failed during instruction: ~A" instr)
                  (error (format "~A" a)))])
            ((lookup-instruction instr) (with-stacks current-state [Exec new-exec])))]
         [(? Literal? lit)
          (define new-state (with-stacks current-state [Exec new-exec]))
          (match lit
            [(? Integer? int) (push-integer int new-state)]
            [(? Float? flt) (push-float flt new-state)]
            [(? Boolean? b) (push-boolean b new-state)])]
         [(? Program-Sequence? ps)
          (with-stacks current-state [Exec (append ps new-exec)])]
         [(and x 0.0) (error (format "how come this didnt match literal predicate? Float? ~A Program? ~A Literal? ~A" (Float? x) (Program? x) (Literal? x)))]))
     (define new-execution-count (+ 1 execution-count))
     (define new-traces (if save-traces (cons exec-top traces) traces))
     (when print
       (printf "~%State after ~A steps (last step: ~A):~%" 
               execution-count (if (list? exec-top) "(...)" (prog->string exec-top)))
       (state-pretty-print next-state))
     (if (> new-execution-count evalpush-limit)
         next-state
         (execute next-state new-execution-count new-traces print))]))

(: make-push-state (-> ProgramState))
(define (make-push-state) (ProgramState '() '() '() '() '() '() '() '()))

(: execute-toplevel (Program -> ProgramState))
(define (execute-toplevel prog)
  (define starting-state (ProgramState `(,prog) '() '() `(,prog) '() '() '() '()))
  (execute starting-state 0 '() #t))

(: run-rush (Program ProgramState Boolean -> ProgramState))
(define (run-rush code state print)
  (define state-with-pushed (if top-level-push-code (push-code code state) state))
  (define state-with-exec (push-exec code state-with-pushed))
  (when print
    (printf "~%State after 0 steps:~%")
    (state-pretty-print state-with-exec))
  (define state-evaluated (execute state-with-exec 0 '() print))
  (define state-with-popped (if top-level-pop-code 
                                (with-stacks state-evaluated 
                                             [Code (match (ProgramState-Code state-evaluated)
                                                     [(cons hd tl) tl]
                                                     ['() '()])]) 
                                state-evaluated))
  state-with-popped)

;; Rush-GP

(struct: 
  Individual 
  ([Program : Program] 
   [Errors : (Listof Float)]
   [Total-Error : (U 'undefined Float)]
   [Scaled-Error : (U 'undefined Float)]))

(: auto-simplify (Program (Program -> (Listof Float)) Integer Boolean Integer -> Individual))
(define (auto-simplify program error-function steps print progress-interval)
  (when print (printf "~%Auto-simplifying with starting size: ~A" (count-points program)))
  (define: (randomly-remove [program : Program]) : Program
    (for/fold ([removed-prog program])
      ([i (in-range (+ 1 (random 2)))])
      (remove-code-at-point removed-prog (rand-int (count-points removed-prog)))))
  (define: (randomly-flatten [program : Program]) : Program
    (define point-index (rand-int (count-points program)))
    (define point (code-at-point program point-index))
    (if (list? point) 
        (insert-code-at-point program point-index (flatten-program point))
        program))
  (define: (print-simplification-report [i : Integer] [errors : (Listof Float)] [program : Program]) : Void
    (when print (printf "~%step: ~A~%program: ~A~%errors: ~A~%total: ~A~%size: ~A~%" 
                        i program errors (apply + errors) (count-points program))))
  (define-values (simplified-errors simplified-program)
    (for/fold: : (values (Listof Float) Program) 
      ([errors (error-function program)]
       [program program])
      ([step (in-range steps)])
      (when (zero? (modulo step progress-interval)) (print-simplification-report step errors program))
      (define new-program  
        (match (random 5)
          [(or 0 1 2 3) (randomly-remove program)]
          [4 (randomly-flatten program)]))
      (define new-errors (error-function new-program))
      (define-values (final-program final-errors)
        (if (> (sum-floats new-errors) (sum-floats errors)) 
            (values program errors) 
            (values new-program new-errors)))
      (values final-errors final-program)))
  (Individual simplified-program simplified-errors (sum-floats simplified-errors) (sum-floats simplified-errors)))

(define: (get-sorter [f : (Individual -> (U Float 'undefined))]) : (Individual -> Float) 
  (λ (i) (match (f i)
           [(? Float? flt) flt]
           [_ 10000.0])))

(: report ((Listof Individual) Integer (Program -> (Listof Float)) Integer -> Individual))
(define (report population generation error-function report-simplifications)
  (printf "~%~%;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;")
  (printf "~%;; -*- Report at generation ~A" generation)
  (define sorted ((inst sort Individual Float) population < #:key (get-sorter Individual-Total-Error)))
  (match-define [cons best _] sorted)
  (printf "~%Best program:~A" (prog->string (Individual-Program best)))
  (printf "~%Partial simplification (may beat best): ~A"
          (prog->string (Individual-Program 
                         (auto-simplify (Individual-Program best) error-function report-simplifications #f 1000))))
  (printf "~%Errors: ~A" (Individual-Errors best))
  (printf "~%Total: ~A" (Individual-Total-Error best))
  (printf "~%Scaled: ~A" (Individual-Scaled-Error best))
  (printf "~%Size: ~A" (count-points (Individual-Program best)))
  (printf "~%~%Average total errors in population: ~A"
          (/ (sum-floats ((inst map Float Individual)  (get-sorter Individual-Total-Error) sorted)) (exact->inexact (length population))))
  (printf "~%Median total errors in population: ~A"
          (Individual-Total-Error (list-ref sorted (trunc (exact->inexact (/ (length sorted) 2))))))
  (printf "~%Average program size in population (points): ~A"
          (/ (sum-floats ((inst map Float Individual) (ann (λ: ([g : Individual]) (exact->inexact (* 1.0 (count-points (Individual-Program g))))) (Individual -> Float)) sorted))
             (exact->inexact (length population))))
  best)

(: generate-tournament-set ((Listof Individual) Integer Integer Integer -> (Listof Individual)))
(define (generate-tournament-set population tournament-size radius location)
  (for/fold: : (Listof Individual)
    ([tournament-set : (Listof Individual) '()])
    ([i (in-range tournament-size)])
    (cons (list-ref population 
                    (if (zero? radius)
                        (rand-int (length population))
                        (modulo (+ location (- (rand-int (+ 1 (* radius 2))) radius)) (length population))))
          tournament-set)))

(: select ((Listof Individual) Integer Integer Integer -> Individual))
(define (select population tournament-size radius location)
  (define tournament-set (generate-tournament-set population tournament-size radius location))
  (define sorted-list ((inst sort Individual Float) tournament-set < #:key (get-sorter Individual-Scaled-Error)))
  (match sorted-list
    [(cons hd _) hd]
    ['() (error "Expected nonempty list in select!")]))

(: select-compensatory ((Listof Individual) Integer Integer Integer Individual -> Individual))
(define (select-compensatory population tournament-size radius location first-parent)
  (define tournament-set (generate-tournament-set population tournament-size radius location))
  (define key-selector (λ: ([ind : Individual]) (sum-floats (map * (Individual-Errors ind) (Individual-Errors first-parent)))))
  (define sorted-list ((inst sort Individual Float) tournament-set (ann < (Float Float -> Boolean)) #:key key-selector))
  (match sorted-list
    [(cons hd _) hd]
    ['() (error "Expected nonempty list in select-compensatory!")]))

(: get-new-individual (Individual Integer Program -> Individual))
(define (get-new-individual old-individual max-points new-program)
  (if (> (count-points new-program) max-points) 
      old-individual 
      (Individual new-program '() 'undefined 'undefined)))

(: mutate (Individual Integer Integer (Listof (U Program (-> Program))) -> Individual))
(define (mutate old-individual mutation-max-points max-points atom-generators)
  (get-new-individual old-individual 
                      max-points 
                      (insert-code-at-point 
                       (Individual-Program old-individual) 
                       (rand-int (count-points (Individual-Program old-individual)))
                       (random-code mutation-max-points atom-generators))))

(: crossover (Individual Individual Integer -> Individual))
(define (crossover parent1 parent2 max-points)  
  (get-new-individual parent1
                      max-points
                      (insert-code-at-point 
                       (Individual-Program parent1) 
                       (rand-int (count-points (Individual-Program parent1)))
                       (code-at-point (Individual-Program parent2)
                                      (rand-int (count-points (Individual-Program parent2)))))))

;; configuration for a pushgp run

(struct: RushGPConfig
  ([Error-Function : (Program -> (Listof Float))]
   [Error-Threshold : Integer]
   [Population-Size : Integer]
   [Max-Points : Integer]
   [Atom-Generators : (Listof Atom-Generator)]
   [Max-Generations : Integer]
   [Mutation-Probability : Float]
   [Mutation-Max-Points : Integer]
   [Crossover-Probability : Float]
   [Simplification-Probability : Float]
   [Tournament-Size : Integer]
   [Scale-Errors : Boolean]
   [Report-Simplifications : Integer]
   [Final-Report-Simplifications : Integer]
   [Reproduction-Simplifications : Integer]
   [Trivial-Geography-Radius : Integer]
   [Compensatory-Mate-Selection : Boolean]))

(: get-default-config (-> RushGPConfig))
(define (get-default-config)
  (RushGPConfig
   (λ (_) (error "Need to specify an error function!"))
   0
   1000
   50
   (append (map definition->instr instructions)
           (list (λ () (ann (random 100) Integer)) (λ () (real->float (random)))))
   1001
   0.4
   20
   0.4
   0.1
   7
   #f
   100
   1000
   25
   0
   #f))

(define-syntax config
  (syntax-rules ()
    ((_ args ...)
     (struct-copy RushGPConfig (get-default-config) args ...))))

(define test-config 
  (config [Error-Function (λ: ([p : Program]) '(10.0))]
          [Population-Size 10000]
          [Tournament-Size 7]))

;; top-level routine
(: rushgp (RushGPConfig -> (U Void Individual)))
(define (rushgp cfg)
  (define error-function (RushGPConfig-Error-Function cfg))
  (define error-threshold (RushGPConfig-Error-Threshold cfg))
  (define population-size (RushGPConfig-Population-Size cfg))
  (define max-points (RushGPConfig-Max-Points cfg))
  (define atom-generators (RushGPConfig-Atom-Generators cfg))
  (define max-generations (RushGPConfig-Max-Generations cfg))
  (define mutation-probability (RushGPConfig-Mutation-Probability cfg))
  (define mutation-max-points (RushGPConfig-Mutation-Max-Points cfg))
  (define crossover-probability (RushGPConfig-Crossover-Probability cfg))
  (define simplification-probability (RushGPConfig-Simplification-Probability cfg))
  (define tournament-size (RushGPConfig-Tournament-Size cfg))
  (define scale-errors (RushGPConfig-Scale-Errors cfg))
  (define report-simplifications (RushGPConfig-Report-Simplifications cfg))
  (define final-report-simplifications (RushGPConfig-Final-Report-Simplifications cfg))
  (define reproduction-simplifications (RushGPConfig-Reproduction-Simplifications cfg))
  (define trivial-geography-radius (RushGPConfig-Trivial-Geography-Radius cfg))
  (define compensatory-mate-selection (RushGPConfig-Compensatory-Mate-Selection cfg))
  (printf "~%Starting RushGP run.~%Error function: ~A~%Error threshold: ~A~%Population size: ~A~%Max points: ~A"
          error-function error-threshold population-size max-points)
  (printf "~%Atom generators: ~A~%Max generations: ~A~%Mutation probability: ~A~%Mutation max points: ~A"
          atom-generators max-generations mutation-probability mutation-max-points)
  (printf "~%Crossover probability: ~A~%Simplification probability: ~A~%Tournament size: ~A" 
          crossover-probability simplification-probability tournament-size)
  (printf "~%Scale errors: ~A" scale-errors)
  (printf "~%Report simplifications: ~A" report-simplifications)
  (printf "~%Final report simplifications: ~A" final-report-simplifications)
  (printf "~%Reproduction simplifications: ~A" reproduction-simplifications)
  (printf "~%Trivial geography radius: ~A" trivial-geography-radius)
  (printf "~%Compensatory mate selection: ~A" compensatory-mate-selection)
  (printf "~%~%")
  (printf "~%Generating initial population...")
  
  (: main-loop (Integer (Listof Individual) (Listof Float) -> (U Individual Void)))
  (define (main-loop generation population historical-total-errors)
    (printf "~%Generation: ~A" generation)
    (cond 
      [(<= generation max-generations)
       (printf "~%Computing errors...")
       (define population-with-errors 
         (map (λ: ([i : Individual])
                (define errors (match (Individual-Errors i)
                                 [(cons _ _) (Individual-Errors i)]
                                 ['() (error-function (Individual-Program i))]))
                (define total-error 
                  (match* ((Individual-Total-Error i) scale-errors)
                    [((? Float? ite) #f) ite]
                    [('undefined _) (keep-number-reasonable (sum-floats errors))]))
                (Individual (Individual-Program i) errors total-error total-error))
              population))
       (define best (report population-with-errors generation error-function report-simplifications))
       (define new-historical-errors (append historical-total-errors (filter Float? `(,(Individual-Total-Error best)))))
       (define ittl-best (Individual-Total-Error best))
       (match (and (Float? ittl-best) (<=  ittl-best error-threshold))
         [#t
          (printf "~%~%SUCCESS at generation ~A~%Successful program: ~A~%Errors: ~A~%Total error: ~A~%Size: ~A~%~%"
                  generation
                  (prog->string (Individual-Program best))
                  (Individual-Errors best)
                  (Individual-Total-Error best)
                  (count-points (Individual-Program best)))
          (auto-simplify (Individual-Program best) error-function report-simplifications #f 1000)]
         [#f 
          (printf "~%Producing offspring...")
          (: new-generation (Listof Individual))
          (define new-generation 
            (for/list 
                ([iteration (in-range population-size)])
              (define n (random))
              (cond [(< n mutation-probability)
                     (mutate (select population-with-errors tournament-size trivial-geography-radius iteration) 
                             mutation-max-points max-points atom-generators)]
                    [(< n (+ mutation-probability crossover-probability))   
                     (define first-parent 
                       (select population-with-errors tournament-size trivial-geography-radius iteration))
                     (define second-parent
                       (if compensatory-mate-selection
                           (select-compensatory population-with-errors tournament-size trivial-geography-radius iteration first-parent)
                           (select population-with-errors tournament-size trivial-geography-radius iteration)))
                     (crossover first-parent second-parent max-points)]
                    [(< n (+ mutation-probability crossover-probability simplification-probability))
                     (auto-simplify
                      (Individual-Program (select population-with-errors tournament-size trivial-geography-radius iteration)) 
                      error-function reproduction-simplifications #f 1000)]
                    [else (select population-with-errors tournament-size trivial-geography-radius iteration)])))
          (main-loop (+ 1 generation) new-generation new-historical-errors)])]
      [else 
       (printf  "~%FAILURE~%")]))
  
  (define: start-population : (Listof Individual)
    (for/list ((iteration (in-range population-size)))
      (Individual (random-code max-points atom-generators) '() 'undefined 'undefined)))
  (define: historical-total-errors : (Listof Float) '())
  
  (main-loop 0 start-population historical-total-errors))

;; evolve a function f(x) = x^2, using the whole instruction set
(: example1 (-> (U Individual Void)))
(define (example1) 
  (rushgp (config [Error-Function
                     (λ: ([program : Program])
                       (for/list: : (Listof Float) ((input (in-range 10.0)))
                         (define state (push-integer input (make-push-state)))
                         (match (ProgramState-Integer (run-rush program state false) )
                           [(cons top-int int-rest)
                            (exact->inexact (abs (- top-int (* input input))))]
                           [_ 1000.0])))])))

;; evolve a function f(x) = x^2, using only integer instructions
(: example2 (-> (U Individual Void)))
(define (example2) 
  (rushgp (config [Error-Function
                     (λ: ([program : Program])
                       (for/list: : (Listof Float) ((input (in-range 10.0)))
                         (define state (push-integer input (make-push-state)))
                         (match (ProgramState-Integer (run-rush program state false))
                           [(cons top-int int-rest)
                            (exact->inexact (abs (- top-int (* input input))))]
                           [_ 1000.0])))]
                    [Atom-Generators 
                     (append (registered-for-type 'integer) 
                             (list (λ () (ann (random 100) Integer)) 
                                   (λ () (real->float (random)))))])))

;; evolve a function f(x) = x!, using integer, exec, boolean instructions, 
;; and an extra input instruction, auxiliary.in
(: example3 (-> (U Individual Void)))
(define (example3)
  (define-instruction auxiliary IN 
    (λ: ([state : ProgramState])
      (match (ProgramState-Auxiliary state)
        [(cons (? Integer? n) _) 
         (push-integer n state)]
        [_ state])))
  (: factorial (Integer -> Integer))
  (define (factorial n) 
    (if (< n 2)
        1
        (* n (factorial (- n 1)))))
  (rushgp (config [Error-Function
                     (λ: ([program : Program])
                       (for/list: : (Listof Float) ((input (in-range 1 6))) 
                         (define state 
                           (with-stacks (make-push-state) 
                                        [Integer `(,input)] 
                                        [Auxiliary `(,input)]))
                         (match (ProgramState-Integer (run-rush program state false))
                           [(cons top-int int-rest)
                            (exact->inexact (abs (- top-int (factorial input))))]
                           [_ 1000000000.0])))]
                    [Atom-Generators
                     (append (registered-for-type 'integer) 
                             (registered-for-type 'exec)
                             (registered-for-type 'boolean)
                             (list (λ () (random 100))
                                   (λ () (real->float (random)))
                                   (λ () 'auxiliary.in)))]
                    [Max-Points 100])))
