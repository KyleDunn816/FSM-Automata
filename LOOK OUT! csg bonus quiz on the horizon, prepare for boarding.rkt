#lang fsm

#|
Design and implement a CSG for L = a^n b^n c^n d^n.

- S: generates words in a^nb^nc^n
- A, G: A promise to generate an a in the context AG.
- B, H: A promise to generate an b in the context BH.
- C, I: A promise to generate an c in the context CI.
- D, K: A promise to generate an d in the context DK.



|#


(define anbncndn-csg
  (make-csg '(S A B C D G H I K) 
            '(a b c d) 
            `((S ,ARROW ABCDS)
              (S ,ARROW K)
              (BA ,ARROW AB) 
              (CA ,ARROW AC) 
              (DA ,ARROW AD) 
              (CB ,ARROW BC)
              (DB ,ARROW BD)
              (DC ,ARROW CD)
              (DK ,ARROW Kd)
              (K  ,ARROW I)
              (CI ,ARROW Ic)
              (I  ,ARROW H)
              (BH ,ARROW Hb)
              (H  ,ARROW G)
              (AG ,ARROW Ga)
              (G ,ARROW ,EMP))
            'S))

(check-derive? anbncndn-csg
               '()
               '(a b c d)
               '(a a b b c c d d)
               '(a a a b b b c c c d d d))





;; Only 'd' right of 'K'
(define (S-INV yield) (eq? (last yield) 'S))
(define (K-INV yield) 
  (andmap (lambda (x) (eq? 'd x))
          (rest (dropf yield (lambda (x) (not (eq? 'K x)))))))
;; Only 'c' and 'd' right of 'I'
(define (I-INV yield) 
  (let* ([cs-ds (rest (dropf yield
                                 (lambda (x) (not (eq? 'I x)))))]
         [ds (dropf cs-ds (lambda (x) (eq? x 'c)))])
    (andmap (lambda (x) (eq? x 'd)) ds)))
(define (H-INV yield)
  (let* ([bs-cs-ds (rest (dropf yield (lambda (x) (not (eq? 'H x)))))]
         [cs-ds (dropf bs-cs-ds (lambda (x) (eq? 'b x)))]
         [ds (dropf cs-ds (lambda (x) (eq? x 'c)))])
    (andmap (lambda (x) (eq? 'd x)) ds)))
(define (G-INV yield)
  (let* ([as-bs-cs-ds (rest (dropf yield (lambda (x) (not (eq? 'G x)))))]
         [bs-cs-ds (dropf as-bs-cs-ds (lambda (x) (eq? 'a x)))]
         [cs-ds (dropf bs-cs-ds (lambda (x) (eq? 'b x)))]
         [ds (dropf cs-ds (lambda (x) (eq? x 'c)))])
    (andmap (lambda (x) (eq? 'd x)) ds)))

(define (in-lang? yield)
  (let* ([as (takef yield (lambda (x) (eq? 'a x)))]
         [bs-cs-ds (dropf yield (lambda (x) (eq? 'a x)))]
         [bs (takef bs-cs-ds (lambda (x) (eq? 'b x)))]
         [cs-ds (dropf bs-cs-ds (lambda (x) (eq? 'b x)))]
         [cs (takef cs-ds (lambda (x) (eq? 'c x)))]
         [ds (dropf cs-ds (lambda (x) (eq? 'c x)))]
         )
    (and (andmap (lambda (x) (eq? 'd x)) ds)
         (= (length as) (length bs) (length cs) (length ds)))))

(define (equal-num-abcd? word)
  (= (+ (count (lambda (x) (eq? 'A x)) word)
        (count (lambda (x) (eq? 'a x)) word))
     (+ (count (lambda (x) (eq? 'B x)) word)
        (count (lambda (x) (eq? 'b x)) word))
     (+ (count (lambda (x) (eq? 'C x)) word)
        (count (lambda (x) (eq? 'c x)) word))
     (+ (count (lambda (x) (eq? 'D x)) word)
        (count (lambda (x) (eq? 'd x)) word))))

(define (no-nt? yield)
  (andmap (lambda (x) (member x (grammar-sigma anbncndn-csg))) yield))


;; Purpose: Determine if loop invariant holds for the given yield
(define (anbncndn-csg-inv yield)
  (and (equal-num-abcd? yield) 
       (implies (member 'S yield) (S-INV yield))
       (implies (member 'G yield) (G-INV yield))
       (implies (member 'H yield) (H-INV yield))
       (implies (member 'I yield) (I-INV yield))
       (implies (member 'K yield) (K-INV yield)) 
       (implies (no-nt? yield) (in-lang? yield)))) 
       
;; (grammar-viz anbncndn-csg '(a a a b b b c c c d d d) anbncndn-csg-inv)

#|
Proof by induction on n=number of derivation step

Base case:
When derivation starts, yield=S.
S-INV holds a S is the rightmost element of the yield) ∧
the number of As, as, Bs, bs, Cs, and cs are all 0 ∧
other implications are true (i.e., false ⇒ X is true)

Inductive Step
Assume: INV holds for n=k
Show: INV holds for n=k+1

S → EMP
By inductive hypothesis INV holds
After applying this production rule:
the number of As, as, Bs, bs, Cs, and cs are all 0 ∧
(implies (no-nt? yield) (in-lang? yield)) holds ∧
other implications are true (i.e., false ⇒ X is true)

S → ABCS
By inductive hypothesis INV holds
After applying this production rule:
|A & a|=|B & b|=|C & c| ∧
S ends the yield ∧
other implications are true (i.e., false ⇒ X is true)

BA → AB, CB → BC, CA → AC
By inductive hypothesis INV holds
After applying any of these production rules:
INV holds because only the ordering of A, B, & C change

S → G
By inductive hypothesis INV holds
After applying this production rule:
|A & a|=|B & b|=|C & c| ∧
Everything to the right of G is c ∧
other implications are true (i.e., false ⇒ X is true)

CG → Gc
By inductive hypothesis INV holds
After applying this production rule:
|A & a|=|B & b|=|C & c| ∧
Everything to the right of G is c+ ∧
other implications are true (i.e., false ⇒ X is true)

BG → BH
By inductive hypothesis INV holds
After applying this production rule:
|A & a|=|B & b|=|C & c| ∧
Everything to the right of H is b∗c+ ∧
other implications are true (i.e., false ⇒ X is true)

BH → Hb
By inductive hypothesis INV holds
After applying this production rule:
|A & a|=|B & b|=|C & c| ∧
Everything to the right of H is b+c+ ∧
other implications are true (i.e., false ⇒ X is true)

AH → AI
By inductive hypothesis INV holds
After applying this production rule:
|A & a|=|B & b|=|C & c| ∧
Everything to the right of I is a∗b+c+ ∧
other implications are true (i.e., false ⇒ X is true)

AI → Ia
By inductive hypothesis INV holds
After applying this production rule:
|A & a|=|B & b|=|C & c| ∧
Everything to the right of I is a+b+c+ ∧
other implications are true (i.e., false ⇒ X is true)

I → EMP
After applying this production rule:
|a|=|b|=|c| ∧
yield is a+b+c+ ∧
other implications are true (i.e., false ⇒ X is true)


Proof that L=L(anbncn)
w∈L ⇔ w∈L(anbncn)
(⇒) Assume w∈L
This means w=anbncn. Given that INV always holds, there
is a derivation such that S generates n ABC, rearranges
ABCs to AnBnCn, and generates w.

(⇐)) Assume w∈L(anbncn)
This means anbncn generated w. Since INV always holds
w=anbncn. Thus, w∈L.

w∈/L ⇔ w∈/L(anbncn)
Contraposition

|#