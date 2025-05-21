#lang fsm

;; FINAL PROJECT FORMAL AUTOMATA
;; BY: Christopher Bernal, Kyle Dunn, and Jonathan Wallace

;code for simple pda below:

;; L = {a^nb^n | n >= 0}
;; States
;; S ci = (listof a) = stack, start state
;; M ci = (append (listof a) (listof b)) AND
;; (length ci as) = (length stack) + (length ci bs)
;; F ci = (append (listof a) (listof b)) and all as and bs matched,
;; final state
;; The stack is a (listof a)
(define a^nb^n
  (make-ndpda '(S M F) '(a b) '(a) 'S '(F)
              `(((S ,EMP ,EMP) (M ,EMP))
                ((S a ,EMP) (S (a)))
                ((M b (a)) (M ,EMP))
                ((M ,EMP ,EMP) (F ,EMP)))
              #:rejects '((b b b) (a b a))
              #:accepts '(() (a b) (a a b b) (a a a b b b) (a a a a a b b b b b))))

;; L = wcw^R | w in (a b)*
;; States
;; S ci is empty and stack is empty
;; P ci = stack^R AND c not in ci
;; Q ci = (append w (list 'c) v) AND
;; w = stack^R v^R
;; F stack = '() AND ci = (append w (list c) w^R)
(define wcw^r (make-ndpda
               '(S P Q F)
               '(a b c)
               '(a b)
               'S
               '(F)
               `(((S ,EMP ,EMP) (P ,EMP))
                 ((P a ,EMP) (P (a)))
                 ((P b ,EMP) (P (b)))
                 ((P c ,EMP) (Q ,EMP))
                 ((Q a (a)) (Q ,EMP))
                 ((Q b (b)) (Q ,EMP))
                 ((Q ,EMP ,EMP) (F ,EMP)))))
;; Tests for wcw^r
(check-reject? wcw^r '(a) '(a c) '(b c a) '(a a b c b a b))
(check-accept? wcw^r '(c) '(a c a) '(a b b b c b b b a))

;; state symbol stacke stacke -> pda-rule
;; Purpose: build a pda-rule
(define (mk-pda-rule from a pop to push)
  (list (list from a pop) (list to push)))

;; pda-rule -> state
;; purpose: Extract from state
(define (get-from r) (first (first r)))

;; pda-rule -> symbol
;; Purpose: Extract read symbol
(define (get-read r) (second (first r)))

;; pda-rule -> stacke
;; Purpose: extract the pop elements
(define (get-pop r) (third  (first r)))

;; pda-rule -> state
;; Purpose: Extract to state
(define (get-to r) (first (second r)))

;; pda-rule -> stacke
;; Purpose: Extract push elements
(define (get-push r) (second (second r)))

;; (listof pda-rule) -> (listof state)
;; Purpose: Extract states in the given rules
(define (extract-states rls)
  (remove-duplicates
   (append-map
    (λ (r) (list (first (first r)) (first (second r))))
    rls)))

;; (listof pda-rule) (listof states) -> (listof pda-rule)
;; Purpose: Replace rules that push more than 2 elements
(define (generate-theta<=2-rules rls sts)
  ;;(listof pda-rule) (listof state) -> (listof pda-rule)
  ;; Purpose: Generate rules with |theta| <= 2 for given rules
  (define (gen-theta<=2-rules theta>2-rules sts)
    ;; pda-rule -> (listof pda-rule)
    ;; Purpose: Generate |theta|  <=2 rules for given rule
    (define (gen-rules r)
      ;; (listof state) (listof symbol) (listof symbol) symbol
      ;; -> (listof pda-rule)
      ;; Purpose: Generate |theta| <=2 rules for given rule
      (define (process-sts sts push pop read)
        (if (= (length sts) 2)
            (list (mk-pda-rule (first sts) read pop (second sts) push))
            (cons (mk-pda-rule (first sts) EMP pop (second sts)
                               (append pop (list (first push))))
                  (process-sts (rest sts) (rest push) pop read))))
      (let* [(from (get-from r)) (read (get-read r)) (pop (get-pop r))
                                 (to (get-to r)) (push (get-push r))
                                 (new-states (build-list
                                              (sub1 (length push))
                                              (λ (i) (gen-state 'T (cons 'T sts)))))
                                 (rev-push (reverse push))]
        (cons (mk-pda-rule from EMP pop (first new-states)
                           (append pop (list (first rev-push))))
              (process-sts (append new-states (list to)) (rest rev-push)
                           pop read))))
    (append-map gen-rules theta>2-rules))
  (let* [(theta>2-rules (filter
                         (λ (r) (and (not (eq? (second (second r)) EMP))
                                     (> (length (second (second r))) 2)))
                         rls))
         (theta<=2-rules (filter (λ (r) (not (member r theta>2-rules)))
                                 rls))]
    (append theta<=2-rules (gen-theta<=2-rules theta>2-rules sts))))

;; (listof pda-rule) (listof symbols) -> (listof pda-rules)
;; purpose: Substitute pop nothing rules with pop 1 rules
(define (generate-beta=1-rules rls gamma)
  (let* [(beta=0-rls (filter (λ (r) (eq? (get-pop r) EMP)) rls))
         (beta>0-rls (filter (λ (r) (not (member r beta=0-rls))) rls))]
    (append beta>0-rls
            (for*/list ([r beta=0-rls]
                        [g gamma])
              (list (list (get-from r) (get-read r) (list g))
                    (list (get-to r)
                          (if (eq? (get-push r) EMP)
                              (list g)
                              (append (get-push r) (list g)))))))))

;;(listof pda-rule) (listof state) -> (listof pda-rule)
;; purpose: Eliminate rules that pop more than two elements
(define (generate-beta<2-rules rules states)
  ;;pda-rule (listof states) -> (listof pda-rule)
  ;;Purpose: Create |beta| = 1 rules for given rule
  (define (convert-beta=1 r states)
    ;; (listof symbol) (listof state) -> (listof pda-rule)
    ;;Purpose: Generate pda rules for given pop list using given states
    (define (gen-intermediate-rules beta sts)
      (if (empty? (rest sts))
          '()
          (cons (mk-pda-rule (first sts) EMP (list (first beta))
                             (first (rest sts)) EMP)
                (gen-intermediate-rules (rest beta) (rest sts)))))
    (let* [(from (get-from r)) (read (get-read r)) (to (get-to r))
                               (beta (get-pop)) (push (get-push))
                               (new-states (build-list
                                            (sub1 (length beta))
                                            (λ (i) (gen-state 'B (cons 'B states)))))]
      (append
       (list
        (mk-pda-rule from EMP (list (first beta)) (first new-states) EMP)
        (mk-pda-rule (last new-states) read (list (last beta)) to push))
       (gen-intermediate-rules (rest beta) new-states))))
  (let* [(beta>=2-rules (filter (λ (r) (and (not  (eq? (get-pop r) EMP))
                                            (>= (length (get-pop r)) 2)))
                                rules))
         (beta<2-rules (filter (λ (r) (not (member r beta>=2-rules))) rules))]
    (append beta<2-rules (append-map (λ (r) (convert-beta=1 r states))
                                     beta>=2-rules))))



;; pda -> pda
;;purpose: Convert given pda to a simple pda.
(define (pda2spda p)
  (let*
      [(pstates (sm-states p))
       (psigma (sm-sigma p))
       (pgamma (sm-gamma p))
       (pstart (sm-start p))
       (pfinals (sm-finals p))
       (prules (sm-rules p))
       (new-start (generate-symbol 'S pstates))
       (new-final (generate-symbol 'F pstates))
       (bottom (generate-symbol 'Z pgamma))
       (initr (mk-pda-rule new-start EMP EMP pstart (list bottom)))
       (frules (map (λ (s) (mk-pda-rule s EMP (list bottom) new-final EMP)) pfinals))
       (beta<2-rules (generate-beta<2-rules prules pstates))
       (beta=1-rules (generate-beta=1-rules beta<2-rules (cons bottom pgamma)))
       (theta<=2-rules (generate-theta<=2-rules beta=1-rules
                                                (extract-states beta=1-rules)))]
    (make-ndpda (append (list new-final new-start)
                        (remove-duplicates
                         (cons pstart (extract-states theta<=2-rules))))
                psigma
                (cons bottom pgamma)
                new-start
                (list new-final)
                (cons initr (append theta<=2-rules frules)))))

(define P1 (pda2spda a^nb^n))
(define P2 (pda2spda wcw^r))

(check-equal? (sm-testequiv? a^nb^n P1) #t)
(check-equal? (sm-testequiv? wcw^r P2) #t)


;; 8. Let sigma = {a, b}
;; Design and implement a pda for:
;; L = {a^mb^n | m,n >=0 and m != n}. Follow all steps of the design recipe

;; S ci = either (listof as) or (listof bs) = stack, Start state
;; M ci = (append (listof as) (listof bs))
;; cond:
;; stack = empty then (length ci as) = (length ci bs)
;; stack = (listof b) then (length ci as) < (length ci bs)
;; stack = (listof a) then (length ci as) > (length ci bs)
;; A ci = (length ci as) > (length ci bs), final state
;; B ci = (length ci bs) > (length ci as), final state
(define a-to-m-b-to-n
  (make-ndpda '(S M A B) '(a b) '(a b) 'S '(A B)
              `(((S a ,EMP) (S (a))) ;;done
                ((S a ,EMP) (A (a))) ;;done
                ((S b (a)) (M ,EMP)) ;;done
                ((S b ,EMP) (B (b))) ;;done
                ((S b ,EMP) (S (b))) ;;done
                ((M b (a)) (M ,EMP)) ;;done
                ((M b ,EMP)(M (b)))  ;;done
                ((M ,EMP (a)) (A ,EMP)) ;;done
                ((M b ,EMP) (B (b))) ;;done
                ((A ,EMP (a)) (A ,EMP))
                ((B ,EMP (b)) (B ,EMP)))
              #:rejects '(() (a a b b) (a b a b) (a b) (a a a b b b) (b a b a) (b b b a a a) (b a) (a b a) (b a b))
              #:accepts '((a a a) (b b b) (a a a b b b b) (a a b b b) (a a a a a b b b) (a a b b b b) (a) (b) (a b b b) (a a a b))))

;;(sm-visualize a-to-m-b-to-n (list 'S S-INV) (list 'M M-INV) (list 'A A-INV) (list 'B B-INV))

;; L = {a^nb^n | n >= 0}
;; States
;; S ci = (listof a) = stack, start state
;; M ci = (append (listof a) (listof b)) AND
;; (length ci as) = (length stack) + (length ci bs)
;; F ci = (append (listof a) (listof b)) and all as and bs matched,
;; final state
;; The stack is a (listof a)
(define a^nb^n-pda
  (make-ndpda '(S M F) '(a b) '(a) 'S '(F)
              `(((S ,EMP ,EMP) (M ,EMP))
                ((S a ,EMP) (S (a)))
                ((M b (a)) (M ,EMP))
                ((M ,EMP ,EMP) (F ,EMP)))
              #:rejects '((b b b) (a b a))
              #:accepts '(() (a b) (a a b b) (a a a b b b) (a a a a a b b b b b))))


;;Example of transforming a spda to a mttm and the following rule conversions
;;Following the example by converting the rules by hand to see what would be needed in order to do the correct computations and rule translations
;;L = a^nb^n
(define a2nb2n-spda-mttm
  (make-mttm
   '(C F-755396 S-755395 S M F Y S-12 S-123 M-12 S-34 S-345 F-5678)
   '(a b Z)
   'C
   '(Y)
   (list
    (list (list 'C (list BLANK BLANK))
          (list 'S-755395 (list RIGHT RIGHT)))
    
    ;;to handle empty transtions that dont read anything with just make a rule that accepts the empty transition and moves to the next state
    ;;This handles the first transition rule that they have.
    ;;((S-755395 ε ε) (S (Z)))
    (list (list 'S-755395 (list 'a BLANK))
          (list 'S (list 'a 'Z)))
    (list (list 'S-755395 (list 'b BLANK))
          (list 'S (list 'b 'Z)))
    (list (list 'S-755395 (list BLANK BLANK))
          (list 'S (list BLANK 'Z)))
    ;;the second transition rule they have
    ;;((M b (a)) (M ε))
    (list (list 'M (list 'b 'a))
          (list 'M-12 (list 'b BLANK)))
    (list (list 'M-12 (list 'b BLANK))
          (list 'M (list RIGHT LEFT)))
    ;;((S ε (Z)) (M (Z))) on empty transitions it is best not to move the head of tape0
    (list (list 'S (list 'a 'Z))
          (list 'M (list 'a 'Z)))
    (list (list 'S (list 'b 'Z))
          (list 'M (list 'b 'Z)))
    (list (list 'S (list BLANK 'Z))
          (list 'M (list BLANK 'Z)))
    
    ;;((S ε (a)) (M (a)))
    (list (list 'S (list 'a 'a))
          (list 'M (list 'a 'a)))
    (list (list 'S (list 'b 'a))
          (list 'M (list 'b 'a)))
    (list (list 'S (list BLANK 'a))
          (list 'M (list BLANK 'a)))

    ;;((S a (Z)) (S (a Z)))
    (list (list 'S (list 'a 'Z))
          (list 'S-34 (list 'a 'Z)))
    (list (list 'S-34 (list 'a 'Z))
          (list 'S-12 (list 'a RIGHT)))
    (list (list 'S-12 (list 'a BLANK))
          (list 'S (list RIGHT 'a)))

    ;;((S a (a)) (S (a a)))
    (list (list 'S (list 'a 'a))
          (list 'S-345 (list 'a 'a)))
    (list (list 'S-345 (list 'a 'a))
          (list 'S-123 (list 'a RIGHT)))
    (list (list 'S-123 (list 'a BLANK))
          (list 'S (list RIGHT 'a)))

    ;;((M ε (Z)) (F (Z)))
    (list (list 'M (list 'a 'Z))
          (list 'F (list 'a 'Z)))
    (list (list 'M (list 'b 'Z))
          (list 'F (list 'b 'Z)))
    (list (list 'M (list BLANK 'Z))
          (list 'F (list BLANK 'Z)))

    ;; ((M ε (a)) (F (a)))
    (list (list 'M (list 'a 'a))
          (list 'F (list 'a 'a)))
    (list (list 'M (list 'b 'a))
          (list 'F (list 'b 'a)))
    (list (list 'M (list BLANK 'a))
          (list 'F (list BLANK 'a)))

    ;;((F ε (Z)) (F-755396 ε))
    (list (list 'F (list 'a 'Z))
          (list 'F-755396 (list 'a BLANK)))
    (list (list 'F (list 'b 'Z))
          (list 'F-755396 (list 'b BLANK)))
    (list (list 'F (list BLANK 'Z))
          (list 'F-755396 (list BLANK BLANK)))

    (list (list 'F-755396 (list BLANK BLANK))
          (list 'F-5678 (list RIGHT LEFT)))
    
    (list (list 'F-5678 (list BLANK BLANK))
          (list 'Y (list BLANK BLANK)))
    )
   2
   'Y))

;;(sm-visualize a2nb2n-spda-mttm)
;;a2nb2n-spda-mttm test
(check-equal? (sm-apply a2nb2n-spda-mttm `(,LM ,BLANK a a b b) 1) 'accept)
(check-equal? (sm-apply a2nb2n-spda-mttm `(,LM ,BLANK a a a) 1) 'reject)
(check-equal? (sm-apply a2nb2n-spda-mttm `(,LM ,BLANK a b b) 1) 'reject)
(check-equal? (sm-apply a2nb2n-spda-mttm `(,LM ,BLANK a a a b b b) 1) 'accept)
(check-equal? (sm-apply a2nb2n-spda-mttm `(,LM ,BLANK a a b b) 1) 'accept)
(check-equal? (sm-apply a2nb2n-spda-mttm `(,LM ,BLANK a b) 1) 'accept)
(check-equal? (sm-apply a2nb2n-spda-mttm `(,LM ,BLANK a b a) 1) 'reject)
(check-equal? (sm-apply a2nb2n-spda-mttm `(,LM ,BLANK a b a b) 1) 'reject)
(check-equal? (sm-apply a2nb2n-spda-mttm `(,LM ,BLANK b b b) 1) 'reject)
(check-equal? (sm-apply a2nb2n-spda-mttm `(,LM ,BLANK a a a b) 1) 'reject)





;                                                                                
;                                                                                
;                                                                                
;                                                                                
;                          ;;;           ;;;;;               ;    ;              
;  ;;; ;;;                 ;;;          ;;;;;;;            ;;;  ;;;              
;  ;;; ;;;     ;;; ;;   ;; ;;;  ;;;;;   ;;; ;;;;;; ;; ;;; ;;;;;;;;;; ;;; ;; ;;;  
;  ;;; ;;;     ;;;;;;; ;;;;;;; ;;;;;;;      ;;;;;;;;;;;;;;;;;;;;;;;; ;;;;;;;;;;; 
;              ;;; ;;; ;;; ;;; ;;  ;;;     ;;; ;;; ;;; ;;; ;;;  ;;;  ;;; ;;; ;;; 
;              ;;; ;;; ;;; ;;;   ;;;;;    ;;;  ;;; ;;; ;;; ;;;  ;;;  ;;; ;;; ;;; 
;  ;;; ;;;     ;;; ;;; ;;; ;;; ;;; ;;;   ;;;   ;;; ;;; ;;; ;;;  ;;;  ;;; ;;; ;;; 
;  ;;; ;;;     ;;;;;;; ;;;;;;; ;;; ;;;  ;;;;;;;;;; ;;; ;;; ;;;; ;;;; ;;; ;;; ;;; 
;  ;;; ;;;     ;;; ;;   ;; ;;;  ;;;;;;  ;;;;;;;;;; ;;; ;;;  ;;;  ;;; ;;; ;;; ;;; 
;   ;;  ;;     ;;;                                                               
;  ;;  ;;      ;;;                                                               
;                                                                                
;                                                                                

;; Constructor at the bottom of this section


;; okay! now i think i know how to write this constructor and the different rule calls but here are some ground rules for each of the type of rules.
;; Since I am starting from a simple pda, I do not have to worry about popping nothing! which means that I dont have to deal with cases of an empty pop!
;; What i do is add a new start and a new final.
;; the new start will have a rule that will simply write a blank and then move to the right.
;; Two states will be added towards the end of the computation as well. The first one will check to see if the computation is BLANK BLANK and then Move the tape0 marker RIGHT and the tape1 marker LEFT 
;; and then move it to a state, making it one state before the final and then check to make sure both the values are BLANK and if this is true then the resulting computation is accepted and sent to the final state.

;; Now what to do with the different push calls that can be made...
;; So this could be split up into six different categories. The first could split it up as follows: inputread-push0 inputread-push1 inputread-push2 
;; or it could be something like empty-read-push0 empty-read-push1 empty-read-push2
;;

;; 0 push rules:
;; blank the element on top and move the LM in tape 1 LEFT.
;; Doing this would require you to add a new state to the computation so that the marker is not moving randomly throughout the computation, and move the tape 0 marker to the right in the new state transition.

;; 1 push rules:
;; push element on top of the stack and dont worry about overwriting the top element because it was going to be popped anyways and move the tape 0 marker to the RIGHT

;; 2 push rules:
;; 3 things need to happen:
;; rule1: overwrite the top element with the first push and transition into a state i make then read the new input, in the stack but dont touch the head of tape0
;; rule2: read the same input with the new top element and move the marker on tape1 RIGHT and transition to the new state.
;; rule3: with the same input with the blank in tape1 you are to write in the value of the second element. and transition to the state written in the original rule.

;; for empty rules it would mostly follow the same structure EXCEPT the head of the input tape0 will not move at all.
;; state state input input action action -> mttm-rule
;; Purpose: To make an mttm-rule
(define (mk-mttm-rule state-in state-out input1 input2 action1 action2)
  (list (list state-in (list input1 input2))
        (list state-out (list action1 action2))))

;; (listof state)(listof pda-rule) E-list ->(list (listof mttm-rule) (listof state))
;; Purpose: Convert the following rules that only have one push and reading some input following mttm-rule equivalence.
;; Accumulator Invariant:
;;     rules = the rest of not yet processed rules,
;;     new-rules = the mttm rules generated so far,
;;     sts = the states generated so far and the initial states that have already been used.
(define (input-read-push0-helper rules new-rules sts)
  (if (empty? rules)
      (list new-rules sts)
      (let* [(rule (first rules))
             (state-in (get-from rule))
             (input1-buffer (get-read rule))
             (input2-buffer (first (get-pop rule)))
             (buffer-state-out (gen-state sts))
             (action1-buffer input1-buffer)
             (action2-buffer BLANK)
             (real-state-out (get-to rule))
             (updated-rules (append (list
                                     (mk-mttm-rule state-in buffer-state-out input1-buffer input2-buffer action1-buffer action2-buffer)
                                     (mk-mttm-rule buffer-state-out real-state-out input1-buffer BLANK RIGHT LEFT)) new-rules))]

        (input-read-push0-helper (rest rules) updated-rules (cons buffer-state-out sts)))))

(check-equal? (input-read-push0-helper (list '((M b (a)) (M ε)) '((S b (a)) (G ε)) '((E b (a)) (F ε)) ) '() '(M S G E F)) '((((E (b a)) (C (b _)))
                                                                                                                             ((C (b _)) (F (R L)))
                                                                                                                             ((S (b a)) (B (b _)))
                                                                                                                             ((B (b _)) (G (R L)))
                                                                                                                             ((M (b a)) (A (b _)))
                                                                                                                             ((A (b _)) (M (R L))))
                                                                                                                            (C B A M S G E F)))
;; (listof pda-rule) (listof state) -> (list (listof mttm-rule) (listof state))
;; Purpose: Convert the following rules that only have one push and reading some input following mttm-rule equivalence.
(define (input-read-push0 rules sts)
  (input-read-push0-helper rules '() sts))

(check-equal? (input-read-push0 (list '((M b (a)) (M ε)) '((S b (a)) (G ε)) '((E b (a)) (F ε)) ) '(M S G E F)) '((((E (b a)) (C (b _)))
                                                                                                                  ((C (b _)) (F (R L)))
                                                                                                                  ((S (b a)) (B (b _)))
                                                                                                                  ((B (b _)) (G (R L)))
                                                                                                                  ((M (b a)) (A (b _)))
                                                                                                                  ((A (b _)) (M (R L))))
                                                                                                                 (C B A M S G E F)))

;; (listof pda-rule) -> (listof mttm-rule)
;; Purpose: converts 1 push rules into mttm 1 push rules.
(define (input-read-push1 rules)
  (if (empty? rules)
      '()
      (let* [(rule (first rules))
             (state-in (get-from rule))
             (state-out (get-to rule))
             (input1 (get-read rule))
             (input2 (first(get-pop rule)))
             (action1 RIGHT)
             (action2 (first (get-push rule)))]
        (append
         (list (mk-mttm-rule state-in state-out input1 input2 action1 action2))
         (input-read-push1 (rest rules))))))

(check-equal? (input-read-push1 '(((S a (b)) (M (a))) ((S b (a)) (M (b))) ((S b (b)) (M (b)))))
              '(((S (a b)) (M (R a))) ((S (b a)) (M (R b))) ((S (b b)) (M (R b))))) 

;;(listof pda-rule) E-list (listof state) -> (list (listof mttm-rule) (listof state))
;; Purpose: Converts 2 push rules into mttm 2 push rules.
;; Accumulator Invariant:
;;     rules = the rest of not yet processed rules,
;;     new-rules = the mttm rules generated so far,
;;     sts = the states generated so far and the initial states that have already been used.
(define (input-read-push2-helper rules new-rules sts)
  (if (empty? rules)
      (list new-rules sts)
      (let* [(rule (first rules))
             (state-in (get-from rule))
             (input1 (get-read rule))
             (input2 (first (get-pop rule)))
             (buffer-state-out (gen-state sts))
             (buffer-state-out2 (gen-state (cons buffer-state-out sts)))
             (pushes (reverse (get-push rule)))
             (push1 (first pushes))
             (push2 (second pushes))
             (real-state-out (get-to rule))
             (updated-rules (append (list
                                     (mk-mttm-rule state-in buffer-state-out input1 input2 input1 push1)
                                     (mk-mttm-rule buffer-state-out buffer-state-out2 input1 push1 input1 RIGHT)
                                     (mk-mttm-rule buffer-state-out2 real-state-out input1 BLANK RIGHT push2)) new-rules))]
        
        (input-read-push2-helper (rest rules) updated-rules (cons buffer-state-out2 (cons buffer-state-out sts))))))

(check-equal? (input-read-push2-helper '(((S a (a)) (S (a a)))) '() '(S)) 
              '((((S (a a)) (A (a a))) ((A (a a)) (B (a R))) ((B (a _)) (S (R a)))) (B A S)))

(check-equal?
 (input-read-push2-helper '(((S a (a)) (S (a a))) ((D a (a)) (C (a a))) ((A a (a)) (S (a a)))) '() '(S C D A))
 '((((A (a a)) (H (a a)))
    ((H (a a)) (I (a R)))
    ((I (a _)) (S (R a)))
    ((D (a a)) (F (a a)))
    ((F (a a)) (G (a R)))
    ((G (a _)) (C (R a)))
    ((S (a a)) (B (a a)))
    ((B (a a)) (E (a R)))
    ((E (a _)) (S (R a))))
   (I H G F E B S C D A)))

;;(listof pda-rule)(listof state) -> (list (listof mttm-rule) (listof state))
;; Purpose: Converts 2 push rules into mttm 2 push rules.
(define (input-read-push2 rules sts)
  (input-read-push2-helper rules '() sts))

(check-equal?
 (input-read-push2-helper '(((S a (a)) (S (a a))) ((D a (a)) (C (a a))) ((A a (a)) (S (a a)))) '() '(S C D A))
 '((((A (a a)) (H (a a)))
    ((H (a a)) (I (a R)))
    ((I (a _)) (S (R a)))
    ((D (a a)) (F (a a)))
    ((F (a a)) (G (a R)))
    ((G (a _)) (C (R a)))
    ((S (a a)) (B (a a)))
    ((B (a a)) (E (a R)))
    ((E (a _)) (S (R a))))
   (I H G F E B S C D A)))

;; TEST BOTH OF THESE FUNCTIONALITIES:

;;((M ε (a)) (F (a)))
;;((M ε (Z)) (F (Z)))
;;((S ε (Z)) (M (Z)))
;;((S ε (a)) (M (a)))

;;((F ε (Z)) (F-755396 ε))
;; pda-rule sigma -> pda-rule
;; Purpose: Converts the pda-rule to read a letter instead of read empty.
(define (parse-rule-for-input-push rule letter)
  (let* [(state-in (get-from rule))
         (state-to (get-to rule))
         (pop-rule (get-pop rule))
         (push-rule (get-push rule))]
    (list (list state-in letter pop-rule) (list state-to push-rule))))

(check-equal? (parse-rule-for-input-push '((M ε (a)) (F (a))) 'a) '((M a (a)) (F (a))))
(check-equal? (parse-rule-for-input-push '((M ε (Z)) (F (Z))) 'b) '((M b (Z)) (F (Z))))
(check-equal? (parse-rule-for-input-push '((M ε (Z)) (F (a b))) 'c) '((M c (Z)) (F (a b))))
(check-equal? (parse-rule-for-input-push '((M ε (a)) (F ε)) 'a) '((M a (a)) (F ε)))

;; pda-rules E-list (listof state) -> (list (listof mttm) (listof state))
;; Purpose: To convert the pda-rules into mttm rules and return the new states used.
;; Accumulator Invariant:
;;     rules = the rest of not yet processed rules,
;;     new-rules = the mttm rules generated so far,
;;     sts = the states generated so far and the initial states that have already been used.
(define (input-parsed-push0 rules new-rules sts)
  (if (empty? rules)
      (list new-rules sts)
      (let* [(rule (first rules))
             (state-in (get-from rule))
             (state-to (get-to rule))
             (pop-rule (first (get-pop rule)))
             (letter-read (get-read rule))
             (push-rule (get-push rule))
             (buffer-state (gen-state sts))
             (updated-rules (append (list
                                     (mk-mttm-rule state-in buffer-state letter-read pop-rule letter-read BLANK)
                                     (mk-mttm-rule buffer-state state-to letter-read BLANK letter-read LEFT))new-rules))]
        (input-parsed-push0 (rest rules) updated-rules (cons buffer-state sts)))))

(check-equal? (input-parsed-push0 '(((S a (a)) (M ε))
                                    ((S c (a)) (F ε))
                                    ((S a (a)) (B ε))) '() '(S M F B))
              '((((S (a a)) (D (a _)))
                 ((D (a _)) (B (a L)))
                 ((S (c a)) (C (c _)))
                 ((C (c _)) (F (c L)))
                 ((S (a a)) (A (a _)))
                 ((A (a _)) (M (a L))))
                (D C A S M F B)))

;; pda-rules -> mttm-rules
;; Purpose: convert push1 pda-rules to mttm-rules that had empty transitions
(define (input-parsed-push1 rules)
  (if (empty? rules)
      '()
      (let* [(rule (first rules))
             (state-in (get-from rule))
             (state-to (get-to rule))
             (pop-rule (if (list? (get-pop rule))
                           (first (get-pop rule))
                           BLANK))
             (letter-read (get-read rule))
             (push-rule (first(get-push rule)))]
        (append
         (list
          (mk-mttm-rule state-in state-to letter-read pop-rule letter-read push-rule))
         (input-parsed-push1 (rest rules))))))

(check-equal? (input-parsed-push1 '(((S a (a)) (M (c)))
                                    ((S c (a)) (F (b)))
                                    ((S a (a)) (B (a))))) '(((S (a a)) (M (a c)))
                                                            ((S (c a)) (F (c b)))
                                                            ((S (a a)) (B (a a)))))

;; pda-rules E-list states -> (list (listof mttm) (listof state))
;; Purpose: To convert the empty transition rules and not move the header
;; Accumulator Invariant:
;;     rules = the rest of not yet processed rules,
;;     new-rules = the mttm rules generated so far,
;;     sts = the states generated so far and the initial states that have already been used.
(define (input-parsed-push2 rules new-rules sts)
  (if (empty? rules)
      (list new-rules sts)
      (let* [(rule (first rules))
             (state-in (get-from rule))
             (input1 (get-read rule))
             (input2 (first (get-pop rule)))
             (buffer-state-out (gen-state sts))
             (buffer-state-out2 (gen-state (cons buffer-state-out sts)))
             (pushes (reverse(get-push rule)))
             (push1 (first pushes))
             (push2 (second pushes))
             (real-state-out (get-to rule))
             (updated-rules (append (list
                                     (mk-mttm-rule state-in buffer-state-out input1 input2 input1 push1)
                                     (mk-mttm-rule buffer-state-out buffer-state-out2 input1 push1 input1 RIGHT)
                                     (mk-mttm-rule buffer-state-out2 real-state-out input1 BLANK input1 push2)) new-rules))]
        (input-parsed-push2 (rest rules) updated-rules (cons buffer-state-out (cons buffer-state-out2 sts))))))


(check-equal? (input-parsed-push2 '(((S a (a)) (M (K a)))
                                    ((S c (a)) (F (a b)))
                                    ((S a (a)) (B (a b)))) '() '(M S F B)) '((((S (a a)) (G (a b)))
                                                                              ((G (a b)) (H (a R)))
                                                                              ((H (a _)) (B (a a)))
                                                                              ((S (c a)) (D (c b)))
                                                                              ((D (c b)) (E (c R)))
                                                                              ((E (c _)) (F (c a)))
                                                                              ((S (a a)) (A (a a)))
                                                                              ((A (a a)) (C (a R)))
                                                                              ((C (a _)) (M (a K))))
                                                                             (G H D E A C M S F B)))

;; pda-rules sigma sts -> (list (listof mttm) (listof state))
;; Converts the read empty rules with 0 push into rules with a letter to read and then converts the rules into mttm-rules
(define (empty-read-push0 rules sigma sts)
  (let [(sig (cons BLANK sigma))]
    (input-parsed-push0 (append-map (λ (rl) (map (λ (si) (parse-rule-for-input-push rl si)) sig)) rules) '() sts)))

(check-equal? (empty-read-push0 '(((M ε (a)) (F ε))
                                  ((M ε (Z)) (F ε))
                                  ((S ε (Z)) (M ε))
                                  ((S ε (a)) (M ε))) '(a b) '(M S F))
              '((((S (b a)) (N (b _)))
                 ((N (b _)) (M (b L)))
                 ((S (a a)) (L (a _)))
                 ((L (a _)) (M (a L)))
                 ((S (_ a)) (K (_ _)))
                 ((K (_ _)) (M (_ L)))
                 ((S (b Z)) (J (b _)))
                 ((J (b _)) (M (b L)))
                 ((S (a Z)) (I (a _)))
                 ((I (a _)) (M (a L)))
                 ((S (_ Z)) (H (_ _)))
                 ((H (_ _)) (M (_ L)))
                 ((M (b Z)) (G (b _)))
                 ((G (b _)) (F (b L)))
                 ((M (a Z)) (E (a _)))
                 ((E (a _)) (F (a L)))
                 ((M (_ Z)) (D (_ _)))
                 ((D (_ _)) (F (_ L)))
                 ((M (b a)) (C (b _)))
                 ((C (b _)) (F (b L)))
                 ((M (a a)) (B (a _)))
                 ((B (a _)) (F (a L)))
                 ((M (_ a)) (A (_ _)))
                 ((A (_ _)) (F (_ L))))
                (N L K J I H G E D C B A M S F)))

;; pda-rules sigma sts ->  (listof mttm)
;; Converts the read empty rules with 0 push into rules with a letter to read and then converts the rules into mttm-rules
(define (empty-read-push1 rules sigma)
  (let [(sig (cons BLANK sigma))]
    (input-parsed-push1 (append-map (λ (rl) (map (λ (si) (parse-rule-for-input-push rl si)) sig)) rules))))

(check-equal? (empty-read-push1 '(((M ε (a)) (F (a)))
                                  ((M ε (K)) (F (a)))
                                  ((M ε (c)) (F (a)))) '(a b))
              '(((M (_ a)) (F (_ a)))
                ((M (a a)) (F (a a)))
                ((M (b a)) (F (b a)))
                ((M (_ K)) (F (_ a)))
                ((M (a K)) (F (a a)))
                ((M (b K)) (F (b a)))
                ((M (_ c)) (F (_ a)))
                ((M (a c)) (F (a a)))
                ((M (b c)) (F (b a)))))

;; pda-rules sigma sts -> (list (listof mttm) (listof state))
;; Converts the read empty rules with 2 push into rules and then convert into mttm rules.
(define (empty-read-push2 rules sigma sts)
  (let [(sig (cons BLANK sigma))]
    (input-read-push2 (append-map (λ (rl) (map (λ (si) (parse-rule-for-input-push rl si)) sig)) rules) sts)))

(check-equal? (empty-read-push2 '(((M ε (a)) (F (a a)))
                                  ((M ε (K)) (F (a b)))
                                  ((M ε (c)) (F (a K)))) '(a b) '(M F))
              '((((M (b c)) (S (b K)))
                 ((S (b K)) (T (b R)))
                 ((T (b _)) (F (R a)))
                 ((M (a c)) (Q (a K)))
                 ((Q (a K)) (R (a R)))
                 ((R (a _)) (F (R a)))
                 ((M (_ c)) (O (_ K)))
                 ((O (_ K)) (P (_ R)))
                 ((P (_ _)) (F (R a)))
                 ((M (b K)) (L (b b)))
                 ((L (b b)) (N (b R)))
                 ((N (b _)) (F (R a)))
                 ((M (a K)) (J (a b)))
                 ((J (a b)) (K (a R)))
                 ((K (a _)) (F (R a)))
                 ((M (_ K)) (H (_ b)))
                 ((H (_ b)) (I (_ R)))
                 ((I (_ _)) (F (R a)))
                 ((M (b a)) (E (b a)))
                 ((E (b a)) (G (b R)))
                 ((G (b _)) (F (R a)))
                 ((M (a a)) (C (a a)))
                 ((C (a a)) (D (a R)))
                 ((D (a _)) (F (R a)))
                 ((M (_ a)) (A (_ a)))
                 ((A (_ a)) (B (_ R)))
                 ((B (_ _)) (F (R a))))
                (T S R Q P O N L K J I H G E D C B A M F)))

;;(listof final-states) state -> mttm-rules
;; Purpose: Connect old-finals to new-final with blank transitions
(define (new-final-transitions old-finals new-final)
  (if (empty? old-finals)
      '()
      (append (list
               (list (list (first old-finals) (list BLANK BLANK))
                     (list new-final (list BLANK BLANK))))
              (new-final-transitions (rest old-finals) new-final))))

(check-equal? (new-final-transitions '(X Y) 'Z)
              '(((X (_ _)) (Z (_ _))) ((Y (_ _)) (Z (_ _)))))

;;Then write the beefy constructor for the whole function:
;;pda -> mttm
;;Convert the given pda to a mttm
(define (pda2mttm a-pda)
  (let* [(s-pda (pda2spda a-pda))
         (a-states (sm-states s-pda))
         (a-sigma (sm-sigma s-pda))
         (a-gamma (sm-gamma s-pda))
         (a-finals (sm-finals s-pda))
         (a-start (sm-start s-pda))
         (a-rules (sm-rules s-pda))
         (input-push0 (filter (λ (rl) (and (not (equal? (get-read rl) EMP)) (equal? (get-push rl) EMP))) a-rules))
         (input-push1 (filter (λ (rl) (and (not (equal? (get-read rl) EMP)) (not (equal? (get-push rl) EMP)) (if (list? (get-push rl))
                                                                                                                 (equal? 1 (length (get-push rl)))
                                                                                                                 #f))) a-rules))
         (input-push2 (filter (λ (rl) (and (not (equal? (get-read rl) EMP)) (not (equal? (get-push rl) EMP)) (if (list? (get-push rl))
                                                                                                                 (equal? 2 (length (get-push rl)))
                                                                                                                 #f))) a-rules))
         (empty-push0 (filter (λ (rl) (and (equal? (get-read rl) EMP) (equal? (get-push rl) EMP))) a-rules))
         (empty-push1 (filter (λ (rl) (and (equal? (get-read rl) EMP) (not (equal? (get-push rl) EMP))
                                           (if (list? (get-push rl))
                                               (equal? 1 (length (get-push rl)))
                                               #f))) a-rules))
         (empty-push2 (filter (λ (rl) (and (equal? (get-read rl) EMP) (not (equal? (get-push rl) EMP))
                                           (if (list? (get-push rl))
                                               (equal? 2 (length (get-push rl)))
                                               #f))) a-rules))
         (input-push0-rules-and-states (input-read-push0 input-push0 a-states))
         (input-push1-rules (input-read-push1 input-push1))
         (input-push2-rules-and-states (input-read-push2 input-push2 (remove-duplicates (append
                                                                                         (second input-push0-rules-and-states)
                                                                                       a-states))))
         (empty-push0-rules-and-states (empty-read-push0 empty-push0 a-sigma (remove-duplicates(append
                                                                                            (second input-push0-rules-and-states)
                                                                                            (second input-push2-rules-and-states)
                                                                                           a-states))))
         (empty-push1-rules (empty-read-push1 empty-push1 a-sigma))
         (empty-push2-rules-and-states (empty-read-push2 empty-push2 a-sigma (remove-duplicates (append (second empty-push0-rules-and-states)
                                                                                                    (append
                                                                                                     (second input-push0-rules-and-states)
                                                                                                     (second input-push2-rules-and-states)) a-states))))
         (states-used (remove-duplicates (append
                                         (second empty-push2-rules-and-states)
                                         (append (second empty-push0-rules-and-states)
                                                 (append
                                                  (second input-push0-rules-and-states)
                                                  (second input-push2-rules-and-states)) a-states))))
         
         (new-final (gen-state states-used))
         (new-start (gen-state  (cons new-final states-used)))
         (all-states-used (cons new-start (cons new-final states-used)))]
    (make-mttm
     all-states-used
     (remove-duplicates (append a-gamma a-sigma))
     new-start
     `(,new-final)
     (append (first input-push0-rules-and-states)
             (append input-push1-rules
                     (append (first input-push2-rules-and-states)
                             (append (first empty-push0-rules-and-states)
                                     (append empty-push1-rules
                                             (append (first empty-push2-rules-and-states)
                                                     (append (list
                                                              (list (list new-start (list BLANK BLANK))
                                                                    (list a-start (list RIGHT RIGHT)))) 
                                                             (new-final-transitions a-finals new-final))))))))
     2
     `,new-final)))

(define a^nb^n-mttm (pda2mttm a^nb^n))
;(sm-visualize a^nb^n-mttm)

(check-equal? (sm-apply a^nb^n-mttm `(,LM ,BLANK a a b b) 1) 'accept)
(check-equal? (sm-apply a^nb^n-mttm `(,LM ,BLANK a a a) 1) 'reject)
(check-equal? (sm-apply a^nb^n-mttm `(,LM ,BLANK a b b) 1) 'reject)
(check-equal? (sm-apply a^nb^n-mttm `(,LM ,BLANK a a a b b b) 1) 'accept)
(check-equal? (sm-apply a^nb^n-mttm `(,LM ,BLANK a b) 1) 'accept)
(check-equal? (sm-apply a^nb^n-mttm `(,LM ,BLANK a b a) 1) 'reject)
(check-equal? (sm-apply a^nb^n-mttm `(,LM ,BLANK b b a) 1) 'reject)
(check-equal? (sm-apply a^nb^n-mttm `(,LM ,BLANK) 1) 'accept)

;(sm-visualize a^nb^n-mttm)
;(sm-rules P1)

;;Test the wcw machine as well:
(define wcw^r-mttm (pda2mttm wcw^r))

(check-equal? (sm-apply wcw^r-mttm `(,LM ,BLANK a a c b b) 1) 'reject)
(check-equal? (sm-apply wcw^r-mttm `(,LM ,BLANK a a c a a) 1) 'accept)
(check-equal? (sm-apply wcw^r-mttm `(,LM ,BLANK a b b c b b a) 1) 'accept)
(check-equal? (sm-apply wcw^r-mttm `(,LM ,BLANK a a a c b b b) 1) 'reject)
(check-equal? (sm-apply wcw^r-mttm `(,LM ,BLANK b b c b b) 1) 'accept)
(check-equal? (sm-apply wcw^r-mttm `(,LM ,BLANK a b c b a) 1) 'accept)
(check-equal? (sm-apply wcw^r-mttm `(,LM ,BLANK a a b b c b b a a) 1) 'accept)
(check-equal? (sm-apply wcw^r-mttm `(,LM ,BLANK) 1) 'reject)

;;the a^nb^m machine where m != n
(define a-to-m-b-to-n-mttm (pda2mttm a-to-m-b-to-n))

(check-equal? (sm-apply a-to-m-b-to-n-mttm `(,LM ,BLANK a a b b) 1) 'reject)
(check-equal? (sm-apply a-to-m-b-to-n-mttm `(,LM ,BLANK a a a a) 1) 'accept)
(check-equal? (sm-apply a-to-m-b-to-n-mttm `(,LM ,BLANK a b b b b a) 1) 'reject)
(check-equal? (sm-apply a-to-m-b-to-n-mttm `(,LM ,BLANK a a a b b b) 1) 'reject)
(check-equal? (sm-apply a-to-m-b-to-n-mttm `(,LM ,BLANK b b b b) 1) 'accept)
(check-equal? (sm-apply a-to-m-b-to-n-mttm `(,LM ,BLANK a b b) 1) 'accept)
(check-equal? (sm-apply a-to-m-b-to-n-mttm `(,LM ,BLANK a a b b b b) 1) 'accept)
(check-equal? (sm-apply a-to-m-b-to-n-mttm `(,LM ,BLANK) 1) 'reject)




;                                                                
;                                                                
;                                                                
;                                                                
;                 ;;;;          ;;;;                 ;;;    ;;;  
;  ;;; ;;;       ;;;;;;        ;;;;;;               ;;;;   ;;;;; 
;  ;;; ;;;      ;;;  ;;;      ;;;                  ;;;;;  ;;; ;;;
;  ;;; ;;;      ;;;  ;;;      ;;; ;;               ; ;;;  ;;; ;;;
;               ;;;  ;;;      ;;;;;;;                ;;;  ;;; ;;;
;               ;;;  ;;;      ;;; ;;;    ;;;;        ;;;  ;;; ;;;
;  ;;; ;;;      ;;; ;;;;      ;;; ;;;    ;;;;        ;;;  ;;; ;;;
;  ;;; ;;;       ;;;;;;        ;;;;;;                ;;;   ;;;;; 
;  ;;; ;;;        ;;;;;;        ;;;;                 ;;;    ;;;  
;   ;;  ;;             ;                                         
;  ;;  ;;                                                        
;                                                                
;                                                                

;; Questions 6 - 10


#|

Q6: How does the mttm start a computation?
  pda2mttm first takes a PDA and converts it to simple form using `pda2spda`.
  Then, it extracts the components of the SPDA for easier reference.
  Next, it filters the rules based on their types, such as:

    - input-push0: transitions that read input but push nothing to the stack
    - input-push1: transitions that read input and push one symbol
    - input-push2: transitions that read input and push two symbols
    - empty-push0: ε-transitions that push nothing
    - empty-push1: ε-transitions that push one symbol
    - empty-push2: ε-transitions that push two symbols

  These categories are processed separately using helper functions like `input-read-push0`, `input-read-push1`, etc., each producing a set of MTTM transitions and updated states.
  After generating transitions for all rule types, it determines which states are used and creates a fresh start state and a fresh accepting (final) state that are unique.
  The key part of how the computation starts is through the addition of a new transition from this `new-start` state:
      (list (list new-start (list BLANK BLANK))
            (list a-start (list RIGHT RIGHT)))

  This rule means: if the machine is in `new-start` and both tape heads are on blanks, move both heads right and enter the SPDA’s actual start state.
  This prepares the MTTM to begin simulating the PDA by positioning the tape heads and transferring control to the PDA logic encoded as MTTM rules.
  Finally, it connects the PDA's original accepting states to the new final state via `new-final-transitions`, and bundles everything into a mttm using make-mttm.

Q7: Outline how pda2mttm accepts and rejects.
  All of the pda's final states are mapped to a new unique final state in the mttm.
  The mttm only accepts in this new final state, which can only occur if the tapes are empty.
  Otherwise, if there are no valid transitions or new-final is not reached, it rejects.

Q8: What are the states for the mttm? What is the relationship with the pda states?
  The states of the mttm are all of the original pda states and the new starting and final states.
  The pda states continue to simulate the pda in the mttm while the starting state begins the simulation and the final state handles acceptance.
  Also, for every rule where a symbol is read and one is popped, but nothing is pushed, a new intermediate state is added to handle the pop and the head movement.
  Similarly, for every rule where 2 symbols are pushed, 2 new intermediate states are added.
  This is because the MTTM can only write one symbol to the stack at a time.

Q9: What is the mttm's input alphabet?
  The mttm's input alphabet is the same as the PDA's input alphabet,
  but it's tape alphabet is the combination of the PDA's input and stack alphabet without duplicates.

Q10: How is the constructed mttm tested?
  The mttm is tested by taking pda's and converting into mttm's through pda2mttm.
  Then each of these are tested on inputs that are known to be accepted or rejected through the pda.
  Makes sure that the mttm matches the acceptance and rejections of the pda.
  Also, each of the helper functions involved have their own test suites to make sure they fulfill their purpose properly.


BIDIRECTIONAL PROOF:

Let P = pda
Let M = pda2mttm(pda)
Prove that the L(P) <--> L(M)
∈ ∉
Lemma 1: w ∈ L(P) <--> w ∈ L(M)

->:
  Assume w ∈ L(P).
  This means that P accepts w, so a sequence of transitions exists in P from its start state to its final/accepting state,
  such that, w is consumed correctly and the stack is properly manipulated.
  By construction of M, all rules of P are converted into MTTM rules that follow one of the six transitions provided by the SPDA.
  These six being input-push0, 1, 2, and empty-push 0, 1, and 2.
  For all MTTM rules, state transitions, and the tapes, input tape and stack tape, are properly manipulated to simulate its corresponding PDA rule in MTTM fashion.
  Thus, since P accepts w, M will simulate this accepting run from P and also accept w.
  Therefore, w ∈ L(M).
  
<-:
  Assume w ∈ L(M).
  This means that M accepts w, so a sequence of transitions exists in M from its start state to its final/accepting state,
  such that, w is consumed correctly and the tapes are properly manipulated.
  Since M comes from pda2mttm, this means that all the transitions in M correspond to one of the transitions of P.
  Thus, an accepting computation in M corresponds to an accepting computation in P.
  This computation consumes the input and manipulates the stack as according to P's original rules.
  Therefore w ∈ L(P).

Lemma 2: w ∉ L(P) <--> w ∉ L(M)

CONTRAPOSITION!

|#

                  
            
              
                
                
    
          

    






