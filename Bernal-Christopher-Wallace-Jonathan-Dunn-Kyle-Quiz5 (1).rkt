#lang fsm

#|

Grade: C-

A constructive proof requires the implementation of a constructor.
You did not implement one. Your theoretical proof sounds plausable,
but leaves out too many details--that would be present in the
implementation of a constructor. For example, how is FINAL-STATE
guaranteed to be a "singular" final state? How are the new
transitions generated? What happens if the input machine has a
single final state? No final states?

|#

#|
Quiz 5 by: Christopher Bernal, Kyle Dunn, Jonathan Wallace

First, we will define a NDFA.
M = (make-ndfa K Σ S F 𝛿)
K = set of states
Σ = Alphabat of the language
S = starting state
F = set of final states
𝛿 = set of transition relations

Now, we will make an equivalent NDFA to M, but with a singular final state
M' = (make-ndfa K' Σ S FINAL-STATE 𝛿')
This new state will be called FINAL-STATE.
So, K will include this new state. Σ and S will be unchanged.
F will only contain FINAL-STATE and 𝛿 will add in the transitions
where all previous final states point to FINAL-STATE with an empty transition.

Prove L(M) = L(M'):
w = word
Lemma 1: w ∈ L(M) <--> w ∈ L(M')
  w ∈ L(M) --> w ∈ L(M'):
    Assume w ∈ L(M)
    A word is accepted in L(M) if the transitions sequence leads to a final state.
      (w S) ⊢*M (() P), where P ∈ F.
    In M', a word is accepted in L(M') the same way but only includes an empty transition to FINAL-STATE.
      (w S') ⊢*M' (() P) ⊢ (() FINAL-STATE), where P ∈ F.
    Since empty transitions do not change the language, the word is unchanged and reaches FINAL-STATE.
    Therefore since the word remains unchanged in the final empty transition,
    w ∈ L(M').
  w ∈ L(M') --> w ∈ L(M):
    Assume w ∈ L(M')
    The word must have reached some original final state in M in order to get to FINAL-STATE in M'.
      (w S') ⊢*M' (() P) ⊢ (() FINAL-STATE), where P ∈ F.
    Since the word reached P and was unchanged by the empty transition to FINAL-STATE,
    w ∈ L(M).

Lemma 2: w ∉ L(M) <--> w ∉ L(M')
  w ∉ L(M) --> w ∉ L(M'):
    Assume w ∉ L(M)
    w is not accepted in L(M) if the transitions sequence does not lead to a final state.
     (w S) ⊢*M (() P), where P ∉ F.
    If w is not accepted in L(M) then it is not accepted in L(M')
    because it is not possible to have the transition to FINAL-STATE since P ∉ F.
     (w S') ⊢*M' (() P) ⊢ (() FINAL-STATE), where P ∈ F.
    The final transition is not possible because the rule where P ∈ F is violated.
    Therefore, since w never reaches FINAL-STATE,
    w ∉ L(M').
  w ∉ L(M') --> w ∉ L(M):
    Assume w ∉ L(M')
    w is not accepted in L(M) if the transitions sequence does not lead to FINAL-STATE.
      (w S') ⊢*M' (() P), where P is not FINAL-STATE
    Since the empty-transition to FINAL-STATE is always taken, as it is the only final state,
    w never reaches a state P, where P ∈ F.
    #|
       w never reaches?
    |#
    Therefore, since w never reaches a state P, where P ∈ F,
    w ∉ L(M).

Therefore, since lemmas 1 and 2 are proven, L(M) = L(M').

|#

;; Example ndfas
(define AT-LEAST-ONE-MISSING (make-ndfa '(S A B C)
                                        '(a b c)
                                        'S
                                        '(A B C)
                                        `((S ,EMP A)
                                          (S ,EMP B)
                                          (S ,EMP C)
                                          (A b A)
                                          (A c A)
                                          (B a B)
                                          (B c B)
                                          (C a C)
                                          (C b C))))

(define AT-LEAST-ONE-MISSING-ONE-FINAL (make-ndfa '(S A B C F)
                                                  '(a b c)
                                                  'S
                                                  '(F)
                                                  `((S ,EMP A)
                                                    (S ,EMP B)
                                                    (S ,EMP C)
                                                    (A b A)
                                                    (A c A)
                                                    (B a B)
                                                    (B c B)
                                                    (C a C)
                                                    (C b C)
                                                    (A ,EMP F)
                                                    (B ,EMP F)
                                                    (C ,EMP F))))

;; Test if the machines produce equal results
(check-equal? (sm-testequiv? AT-LEAST-ONE-MISSING AT-LEAST-ONE-MISSING-ONE-FINAL 500)
              #t)

