#lang fsm

#|
Grade: B+

There are some inconsistencies between your answers for different steps
of the DR. In addition, your proof is not entirely clear. See comments
in your code.

|#

;; Quiz 4 by Christopher Bernal, Kyle Dunn, and Jonathan Wallace

;; L = {w | w represents a proper even binary number}
;; Name: BIN-EVEN
;;
;; Alphabet(1 0)
;;
;; States:
#|
   None of your state roles reflect that the consumed input
   is a proper even binary number.
|#
;; S: nothing detected, start state
;; A: 0 has been detected in the starting state, final state
;; O: 1 has been detected after the starting state
;; F: 0 has been detected after the O state, final state
(define BIN-EVEN (make-dfa `(S A O F ,DEAD)
                      '(1 0)
                      'S
                      '(F A)
                      `((S 1 O)
                        (S 0 A)
                        (A 1 ,DEAD)
                        (A 0 ,DEAD)
                        (O 0 F)
                        (O 1 O)
                        (F 1 O)
                        (F 0 F)
                        (,DEAD 0 ,DEAD)
                        (,DEAD 1 ,DEAD))
                      'no-dead))


;; Test for BIN-EVEN
#|
   Just curious, why not use the shorter version of testing
   using #:accepts and #:rejects ?
|#
(check-equal? (sm-apply BIN-EVEN '(1 0 1 1 0)) 'accept) ; 22
(check-equal? (sm-apply BIN-EVEN '(0 1 1 0 1 1 0)) 'reject) ;; improper 56
(check-equal? (sm-apply BIN-EVEN '(1 1 0 0 1 0 0 1 1)) 'reject) ;; 403
(check-equal? (sm-apply BIN-EVEN '(0)) 'accept) ;; 0
(check-equal? (sm-apply BIN-EVEN '(0 0 1 1)) 'reject) ;; improper 3
(check-equal? (sm-apply BIN-EVEN '(0 0)) 'reject) ;; improper 0
(check-equal? (sm-apply BIN-EVEN '(0 1 1 0 0 0 1 1 1 1)) 'reject) ;; improper 399
(check-equal? (sm-apply BIN-EVEN '(1 1)) 'reject) ;; 3
(check-equal? (sm-apply BIN-EVEN '(1)) 'reject) ;; 1
(check-equal? (sm-apply BIN-EVEN '(1 0 0 0 1 1 1 0 0 1 0)) 'accept) ;; 1138
(check-equal? (sm-apply BIN-EVEN '()) 'reject) ;; empty
(check-equal? (sm-apply BIN-EVEN '(1 1 1 1 1 1 1 0)) 'accept) ;; 254

;; Random Testing
(sm-test BIN-EVEN 10)

;; INVARIANTS

;; S-INV - ci has not been consumed, it is the starting state
;; Purpose: Detect if the consumed input has not had any consumed elements.
(define (S-INV ci)
  #|
     Why do you need a conditional statement? No decision is
     being made. It suffices for the body to be: (= (length ci) 0)
  |#
  (if (= (length ci) 0)
      #t
      #f))

(check-equal? (S-INV '()) #t)
(check-equal? (S-INV '(1)) #f)
(check-equal? (S-INV '(0 1 0 1)) #f)
(check-equal? (S-INV '(1 0)) #f)

;; A-INV - ci has consumed one character, this character is 0.
;; Purpose: Detect if the consumed input is only the binary number 0.
(define (A-INV ci)
  (and (>= (length ci) 1)
       (= (first ci) 0)))

(check-equal? (A-INV '()) #f)
(check-equal? (A-INV '(1)) #f)
(check-equal? (A-INV '(1 0 0 1)) #f)
(check-equal? (A-INV '(1 1)) #f)
(check-equal? (A-INV '(0)) #t)

;; DEAD-INV - ci has consumed two characters, the first being 0.
;; Purpose: Detect if the consumed input is an improper binary number. 
(define (DEAD-INV ci)
  (and (>= (length ci) 2)
       (= (first ci) 0)))

(check-equal? (DEAD-INV '()) #f)
(check-equal? (DEAD-INV '(1)) #f)
(check-equal? (DEAD-INV '(0)) #f)
(check-equal? (DEAD-INV '(0 0)) #t)
(check-equal? (DEAD-INV '(0 1 1 0 1)) #t)
(check-equal? (DEAD-INV '(1 1 1 0 1)) #f)

;; O-INV - ci starts with a 1 and is a proper binary number that is odd
;; Purpose: Detect if the consumed input is a proper binary number that is odd.
#|
   This is correct, but it does not correspond to your result for O
   listed for Step 3 of the DR.
|#
(define (O-INV ci)
  (and (>= (length ci) 1)
       (= (first ci) 1)
       (= (last ci) 1)))

(check-equal? (O-INV '()) #f)
(check-equal? (O-INV '(1)) #t)
(check-equal? (O-INV '(0)) #f)
(check-equal? (O-INV '(1 1)) #t)
(check-equal? (O-INV '(0 1 1 0 1)) #f)
(check-equal? (O-INV '(1 1 1 0 1)) #t)

;; F-INV - ci is a proper binary number that is even (ends with 0)
;; Purpose: Detect if the consumed input is a proper binary number that is even.
#|
   This is better, but it does not correspond to your result for F
   listed for Step 3 of the DR.

   Why are you using a conditional expression?

   Why are you testing if the ci is '(0)? It can't be '(0) if the
   machine is in F!
|#
(define (F-INV ci)
  (if (equal? ci '(0))
      #t
      (and (>= (length ci) 1)
           (= (first ci) 1)
           (= (last ci) 0))))

(check-equal? (F-INV '()) #f)
(check-equal? (F-INV '(0)) #t)
(check-equal? (F-INV '(1)) #f)
(check-equal? (F-INV '(0 1 1 0)) #f)
(check-equal? (F-INV '(1 1 0 1 0)) #t)

#| PROOF
Proof by induction on n = the number of steps M performs to consume w.
Base case: n = 0
    If n is 0, then the consumed input is '(). This means that S-INV holds
    because the length of ci is 0.
Inductive step:
    Assume that the state invariants hold for n = k.
    Show that the state invariants hold for n = k + 1
    If n = k + 1, the consumed input can not be the empty list so our machine must
    have consumed at least one symbol.
    equation from page 105 basically says that that the state the machine is in
    with the consumed input
    the initial state with the first symbol of w and the rest,
    which takes k transitions to get state r. Meaning at state r only a remains.
    Then it takes one transition
    to get to the final state q. We are proving the final transition.

Transition 1: (S 1 O)
    By inductive hypothesis, S-INV holds. Consuming a 1 means that the consumed
    input is a proper binary number that is currently odd.
    Therefore, we may conclude that O-INV holds after 1 is consumed. 
Transition 2: (S 0 A)
    By inductive hypothesis, S-INV holds. Consuming a 0 means that the consumed
    input is binary number 0.
    Therefore, we may conclude that A-INV holds after 0 is consumed. 
Transition 3: (A 1 ,DEAD)
    By inductive hypothesis, A-INV holds. Consuming a 1 means that the consumed
    input is an improper binary number.
    Therefore, we may conclude that DEAD-INV holds after 1 is consumed.                     
Transition 4: (A 0 ,DEAD)
    By inductive hypothesis, A-INV holds. Consuming a 0 means that the consumed
    input is an improper binary number.
    Therefore, we may conclude that DEAD-INV holds after 0 is consumed.                    
Transition 5: (O 0 F)
    By inductive hypothesis, O-INV holds. Consuming a 0 means that the consumed
    input is a proper binary number that is even.
    Therefore, we may conclude that F-INV holds after 0 is consumed.
Transition 6: (O 1 O)
    By inductive hypothesis, O-INV holds. Consuming a 1 means that the consumed
    input is a proper binary number that is odd.
    Therefore, we may conclude that O-INV still holds after 1 is consumed.
Transition 7: (F 1 O)
    By inductive hypothesis, F-INV holds. Consuming a 1 means that the consumed
    input is a proper binary number that is odd.
    Therefore, we may conclude that O-INV holds after 1 is consumed.
Transition 8: (F 0 F)
    By inductive hypothesis, F-INV holds. Consuming a 0 means that the consumed
    input is a proper binary number that is even.
    Therefore, we may conclude that F-INV still holds after 0 is consumed.
Transition 9: (,DEAD 0 ,DEAD)
    By inductive hypothesis, DEAD-INV holds. Consuming a 0 means that the consumed
    input is an improper binary number.
    Therefore, we may conclude that DEAD-INV still holds after 0 is consumed.
Transition 10: (,DEAD 1 ,DEAD)
    By inductive hypothesis, DEAD-INV holds. Consuming a 1 means that the consumed
    input is an improper binary number.
    Therefore, we may conclude that DEAD-INV still holds after 1 is consumed.

LEMMA 1:
1. w ∈ L ↔ w ∈ L(O)
2. w ∉ L ↔ W ∉ L(O)

Assume w ∈ L.
When w ∈ language, this means that w is a proper and even binary number.
The proof that the state invariants hold when w is consumed means that O can only
halt in F or A, which is the final states of zero or a proper and even binary number.
Therefore, w ∈ L.
     Do you mean that BIN-EVEN, not O, can only halt in F or A?

Assume w ∈ L(O).
0 is a state, not a machine. A state does not represent a language.
Instead of O, do you mean BIN-EVEN?

w ∈ L(O) means that O only halts in F or A. A's invariant guarantees that w is 0
and F's invariant guarantees that w is an even proper binary number.
Therefore, w ∈ L.

Lemma 2:
Assume w ∉ L.
w ∉ L means that w does not have a proper even binary number. Since we know that
the state invariants hold, O [O?] does not halt in F or A after consuming w.
Since F and A are the only final states, we have that w ∉ L(O).

Assume w ∉ L(O).
O does not halt in F or A. Given that the state invariants always hold, this means
that w is not a proper and even binary number. Therefore, w ∉ L.

L = L(BIN-EVEN)
Lemmas 1 and 2 establish the theorem.

|#

