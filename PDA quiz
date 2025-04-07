#lang fsm

#|
Grade: A-

Good job! See comments in your proofs.
|#

;; 8. Let sigma = {a, b}
;; Design and implement a pda for:
;; L = {a^mb^n | m,n >=0 and m != n}. Follow all steps of the design recipe

;; S ci = (listof as) or (listof bs) = stack, Start state
;; M ci = (append (listof as) (listof bs))
#|
   Use implications to express such conditions
|#
;; cond:
;; stack = empty then (length ci as) = (length ci bs)
;; stack = (listof b) then (length ci as) < (length ci bs)
;; stack = (listof a) then (length ci as) > (length ci bs)
;; A ci = (length ci as) > (length ci bs), final state
;; B ci = (length ci bs) > (length ci as), final state

(define a-to-m-b-to-n
  (make-ndpda '(S M A B) '(a b) '(a b) 'S '(A B)
              `(((S a ,EMP) (S (a)))
                ((S a ,EMP) (A (a)))
                ((S b (a)) (M ,EMP))
                ((S b ,EMP) (B (b)))
                ((S b ,EMP) (S (b)))
                ((M b (a)) (M ,EMP))
                ((M b ,EMP)(M (b)))
                ((M ,EMP (a)) (A ,EMP))
                ((M b ,EMP) (B (b)))
                ((A ,EMP (a)) (A ,EMP))
                ((B ,EMP (b)) (B ,EMP)))
              #:rejects '(() (a a b b) (a b a b) (a b) (a a a b b b) (b a b a) (b b b a a a) (b a) (a b a) (b a b))
              #:accepts '((a a a) (b b b) (a a a b b b b) (a a b b b) (a a a a a b b b) (a a b b b b) (a) (b))))


;; ci stack -> boolean
;; purpose: checks to see if the ci and stck are equal in length and if the stck ci contain the same letters.
;; which can either be only as or only bs
(define (S-INV ci stck)
  (and (equal? (length ci) (length stck)) 
       (or (andmap (λ (x y) (and (equal? 'a x) (equal? 'a y))) ci stck)
           (andmap (λ (x y) (and (equal? 'b x) (equal? 'b y))) ci stck))))

(check-equal? (S-INV '() '()) #t)
(check-equal? (S-INV '(a b a b) '()) #f)
(check-equal? (S-INV '() '(a b a b)) #f)
(check-equal? (S-INV '(a a a a) '(a a a a)) #t)
(check-equal? (S-INV '(b b b b) '(b b b b)) #t)
(check-equal? (S-INV '(a a a a) '(b b b b)) #f)
(check-equal? (S-INV '(b b b b) '(a a a a)) #f)
(check-equal? (S-INV '(a a a b) '(a a a b)) #f)

;; ci stck -> boolean
;; purpose: determines if the ci has as before bs and checks to see if the M State conditional holds
(define (M-INV ci stck)
  (let* [(as (filter (λ (x) (equal? 'a x)) ci))
         (bs (filter (λ (x) (equal? 'b x)) ci))
         (as-before-bs-ci? (equal? ci (append as bs)))]
    #|
       This is better expressed using the function implies: (and (implies ...)
                                                                 (implies ...)
                                                                 (implies ...))
    |#
    (cond
      [(empty? stck) (and (equal? (length as) (length bs)) as-before-bs-ci?)]
      [ (andmap  (λ (x) (equal? 'a x)) stck)
        (and (> (length (append as stck)) (length bs)) as-before-bs-ci?)]
      [(andmap  (λ (x) (equal? 'b x)) stck)
       (and as-before-bs-ci? (> (length (append bs stck)) (length as)))]
      [else #f])))

(check-equal? (M-INV '() '()) #t)
(check-equal? (M-INV '(a a b b) '()) #t)
(check-equal? (M-INV '(a a a b b b b) '(b)) #t)
(check-equal? (M-INV '(a a a b b) '(a)) #t)
(check-equal? (M-INV '(a b a b) '()) #f)
(check-equal? (M-INV '(b b b b) '(b b b b)) #t)
(check-equal? (M-INV '(a a a b) '(a a)) #t)
(check-equal? (M-INV '(a a a) '(a b a b)) #f)
(check-equal? (M-INV '(a a a b b) '()) #f)

;; ci stck -> boolean
;; purpose: Determine if the stack contains only as and that there are more as in the ci than bs
(define (A-INV ci stck)
  (let* [(as (filter (λ (x) (equal? 'a x)) ci))
         (bs (filter (λ (x) (equal? 'b x)) ci))
         (as-before-bs-ci? (equal? ci (append as bs)))
         (contains-only-as? (andmap (λ (x) (equal? x 'a)) stck))]
    (and as-before-bs-ci? contains-only-as? (> (length as) (length bs)))))

(check-equal? (A-INV '() '()) #f)
(check-equal? (A-INV '(a b a a) '()) #f)
(check-equal? (A-INV '(a a a b b) '(a)) #t)
(check-equal? (A-INV '(a a a a a b b) '(a a a)) #t)
(check-equal? (A-INV '(b b b b a a a a) '()) #f)
(check-equal? (A-INV '(a a a a b b b b) '()) #f)
(check-equal? (A-INV '(a a a a b b b) '(a)) #t)
(check-equal? (A-INV '(a b a b) '()) #f)
(check-equal? (A-INV '(a a a a a a b b b b b) '(a)) #t)


;; ci stck -> boolean
;; purpose: Determine if the stack contains only as and that there are more as in the ci than bs
(define (B-INV ci stck)
  (let* [(as (filter (λ (x) (equal? 'a x)) ci))
         (bs (filter (λ (x) (equal? 'b x)) ci))
         (as-before-bs-ci? (equal? ci (append as bs)))
         (contains-only-bs? (andmap (λ (x) (equal? x 'b)) stck))]
    (and as-before-bs-ci? contains-only-bs? (> (length bs) (length as)))))

(check-equal? (B-INV '() '()) #f)
(check-equal? (B-INV '(a b a a) '()) #f)
(check-equal? (B-INV '(a a a b b) '(a)) #f)
(check-equal? (B-INV '(a a a a a b b) '(a a a)) #f)
(check-equal? (B-INV '(b b b b a a a a) '()) #f)
(check-equal? (B-INV '(a a a a b b b b) '()) #f)
(check-equal? (B-INV '(a a a a b b b) '(a)) #f)
(check-equal? (B-INV '(a b a b) '()) #f)
(check-equal? (B-INV '(a a a a a a b b b b b) '(a)) #f)
(check-equal? (B-INV '(a a a a b b b b b) '(b)) #t)
(check-equal? (B-INV '(a a b b b b b) '(b b b)) #t)
(check-equal? (B-INV '(a a b b b) '()) #t)
(check-equal? (B-INV '(a a a b b b b) '(b)) #t)


;; (sm-visualize a-to-m-b-to-n (list 'S S-INV) (list 'M M-INV) (list 'A A-INV) (list 'B B-INV))
;; ((S a ,EMP) (A (a))) ((S b ,EMP) (B (b)))

;; PROOF:
;; M = a-to-m-b-to-n
;; L = a^mb^n where m,n >= 0 and m != n
;; ci = consumed input
;; w ∈ (sm-sigma a-to-m-b-to-n)
;; F = (sm-finals a-to-m-b-to-n)
;; P = a^mb^n where m,n >= 0 and m != n

;; Theorem: State invariants hold when M accepts w

#|
   Induction on what?
|#

#|
Base case:
   S-INV holds because the consumed input and stack are both empty.

Inductive case:
((S a ,EMP) (S (a))):
   By IH, S-INV holds. After performing the rule, ci = a and stck = a.
   S-INV still holds because ci and stck are equal in length and characters.
((S a ,EMP) (A (a)))
   By IH, S-INV holds. After performing the rule, ci = a and stck = a.
   A-INV holds because stck only contains a's and ci has more a's than b's.
((S b (a)) (M ,EMP))
   By IH, S-INV holds. After performing the rule, ci = a b and stck is empty.
   M-INV holds because ci contains a before b and the number of a's and b's are equal.
((S b ,EMP) (B (b)))
   By IH, S-INV holds. After performing the rule, ci = b and stck = b.
   B-INV holds because stck contains only b’s and ci has more b’s than a’s.
((S b ,EMP) (S (b)))
   By IH, S-INV holds. After performing the rule, ci = b and stck = b.
   S-INV still holds because ci and stck are equal in length and characters.
((M b (a)) (M ,EMP))
   By IH, M-INV holds. After performing the rule, ci = a b and stck is empty.
   M-INV still holds because ci contains a before b and the number of a's and b's are equal.
((M b ,EMP)(M (b)))
   By IH, M-INV holds. After performing the rule, ci = a b and stck = b.
   M-INV still holds because ci contains a before b and the number of b's exceeds the number of a's.
((M ,EMP (a)) (A ,EMP))
   By IH, M-INV holds. After performing the rule, ci = a a b and stck is empty.
   A-INV holds because ci has more a's than b's and stck contains only a’s.
((M b ,EMP) (B (b)))
   By IH, M-INV holds. After performing the rule, ci = a b b and stck = b.
   B-INV holds because stck contains only b’s and ci has more b’s than a’s.
((A ,EMP (a)) (A ,EMP))
   By IH, A-INV holds. After performing the rule, ci = a a and stck is empty.
   A-INV still holds because ci has more a’s than b’s.
((B ,EMP (b)) (B ,EMP))
   By IH, B-INV holds. After performing the rule, ci = b b and stck is empty.
   B-INV still holds because ci has more b’s than a’s.

Prove L = L(M)

Lemma: w ∈ L <-> w ∈ L(M)

->: Assume w ∈ L. This means that w = a^m b^n where m != n. Given that the
invariants always hold, we get
Case 1: m > n (More a’s than b’s)
 (S, a^m b^n, EMP) ⊢^m (S, b^n, a^m) ⊢^n (M, EMP, a^(m-n)) ⊢* (A, EMP, a^(m-n))
#|
   This is not correct. What if n=0?
|#

Case 2: n > m (More b’s than a’s)
 (S, a^m b^n, EMP) ⊢^m (S, b^n, a^m) ⊢^n (M, EMP, b^(n-m)) ⊢* (B, EMP, b^(n-m))
#|
   This is not correct. What if m=0?
|#


Therefore, in both cases, w ∈ L(M).

<-: Assume w ∈ L(M). This means that M halfs in either A or B, the final states,
                                    #| halfs? |#
with an empty stack that has consumed w. Since invariants always hold,
w = a^m b^n where m != n.

Therefore, w ∈ L.

Lemma: w ∉ L <-> w ∉ L(M)

->: Assume w ∉ L. This means that w != a^m b^n where m != n. Since the
invariants always hold, there are no possible ways
for M to consume w and end in either A or B with an empty stack.
         #| not consume, but accept |#

Therefore, w ∉ L(M)

<-: Assume w ∉ L(M). This means that M cannot transition into either A or B with
an empty stack having consumed w.
Since the invariants always hold, this means that w is not a^m b^n where m != n.

Therefore, w ∉ L.
|#











