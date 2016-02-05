#lang racket

; =============================
; COMPILER: into low-level code
; (only for o->o case)
; =============================

; NPR
(define ongexp+labels
'(A :lambda ()
  (B :@
   ((C :lambda (m n s z)
     (D : m
      ((E :lambda (a)
       (F : n
        ((G :lambda (b) (H : s ((I :lambda () (J : b ())))))
         (K :lambda () (L : a ())))))
       (M :lambda () (N : z ())))))
    (O :lambda (f c)
     (P : f ((Q :lambda () (R : f ((S :lambda () (T : f ((U :lambda () (V : c ())))))))))))
    (W :lambda (g v) (X : g ((Y :lambda () (Z : g ((AA :lambda () (AB : v ()))))))))
    (AC :lambda (e) (AD : t ((AE :lambda () (AF : e ())))))
    (AG :lambda () (AH : y ()))
    )))
  )


;mult 3 2
#;(define ongexp+labels
'(A :lambda ()
  (B :@
   ((C :lambda (m n s z)
     (D : m
      ((E :lambda (a)
       (F : n
        ((G :lambda (b) (H : s ((I :lambda () (J : b ())))))
         (K :lambda () (L : a ())))))
       (M :lambda () (N : z ())))))
    (O :lambda (f c)
     (P : f ((Q :lambda () (R : f ((S :lambda () (T : f ((U :lambda () (V : c ())))))))))))
    (W :lambda (g v) (X : g ((Y :lambda () (Z : g ((AA :lambda () (AB : v ()))))))))
    (AC :lambda (e) (AD : t ((AE :lambda () (AF : e ())))))
    (AG :lambda () (AH : y ()))
    )))
  )
;mult
#;(define ongexp+labels
'(A :lambda ()
  (B :@
   ((C :lambda (m n s z)
     (D : m
      ((E :lambda (a)
       (F : n
        ((G :lambda (b) (H : s ((I :lambda () (J : b ())))))
         (K :lambda () (L : a ())))))
       (M :lambda () (N : z ())))))
    (O :lambda (f c)
     (P : m1 ((Q :lambda (z1) (R : f ((S :lambda () (T : z1 ()))))) (U :lambda () (V : c ())))))
    (W :lambda (g v)
     (X : n1 ((Y :lambda (z2) (Z : g ((AA :lambda () (AB : z2 ()))))) (AA1 :lambda () (AB1 : v ())))))
    (AC :lambda (e) (AD : t ((AE :lambda () (AF : e ())))))
    (AG :lambda () (AH : y ()))
    )))
  )

#;(define ongexp+labels
'(A :@ ((B :lambda (n) (C : n ()))
        (D :lambda () (E : s ()))))
  )

; s:o->o ---> \ a1 . s a1
#;(define ongexp+labels
'(A :lambda () (B : s ((C :lambda () (D : a1 ())))))
  )

; g @ (\n . n)
#;(define ongexp+labels
'(A : g ((B :lambda (n) (C : n ()))))
  )

;succ
#;(define ongexp+labels
'(A :lambda ()
    (B : s ((C :lambda () (D :@ ((E :lambda () (F : n ((G :lambda (a1) (H : s ((I :lambda () (J : a1()))))))))
                                 (K :lambda () (L : z ())))))
            ))
  ))
#;(define ongexp+labels
'(A :lambda ()
    (B : s ((C :lambda () (D : n ((E :lambda (a1) (F : s ((G :lambda () (H : a1())))))
                                  (I :lambda () (J : z ()))))))
            )))
#;(define ongexp+labels
'(A :lambda ()
    (B :@ ((C :lambda (n s z)
              (D : s ((E :lambda () (F : n ((G :lambda (a1) (H : s ((I :lambda () (J : a1 ())))))
                                         (K :lambda () (L : z ()))))))))
           (M :lambda (s1 z1) (N : m ((O :lambda (a2) (P : s1 ((Q :lambda () (R : a2 ())))))
                                      (S :lambda () (T : z1 ())))))
           (U :lambda (z2) (V : s2 ((W :lambda () (X : z2 ())))))
           (Y :lambda () (Z : z4 ()))
           ))
  ))

;succ2
#;(define ongexp+labels
'(Root :lambda ()
    (App :@
         ((A :lambda (n) (B : s ((C :lambda () (D : n ((E :lambda (a1) (F : s ((G :lambda () (H : a1())))))
                                  (I :lambda () (J : z ()))))))))
          (K :lambda (s1 z1) (L : s1 ((M :lambda () (N : s1 ((O :lambda () (P : z1 ())))))))))
    )))


(define (get-index l i)
  (match l
    [`(,x . ,y) (if (equal? x i) 1 (+ 1 (get-index y i)))]
    [`() (error "get-index: empty list")]))

(define st-get dict-ref)
(define st-has? dict-has-key?)
(define st-set dict-set)
(define st-empty  #hash())
(define (Generate-code lnf)
  (append (Generate-code-auxiliary lnf) (Generate-code1 lnf st-empty) `((reverse (,(car lnf) (quote ((,(car lnf), 0))))))))
(define (Generate-code1 lnf static-binders)
  (match lnf
    [`(,l :lambda ,args ,lnfs)
     (for-each (λ (arg) (set! static-binders (st-set static-binders arg `(,l ,(get-index args arg))))) args)
       (match lnfs
         [`(,ln :@ ,As) (cons `(define (,l t) (,ln (cons (list (quote ,ln) 0) t)))
                               (Generate-code1 lnfs static-binders))]
         [`(,ln : ,var ,As)
          (if (st-has? static-binders var)
              (let ([bind (st-get static-binders var)])
                (cons `(define (,l t) (,ln (cons (list (quote ,ln) (FQ (quote ,(car bind)) t)) t)))
                      (Generate-code1 lnfs static-binders)))
              (cons `(define (,l t) (,ln (cons (list (quote ,ln) 1) t)))
                    (Generate-code1 lnfs static-binders)))])]
    [`(,l :@ ,lnfs) (let ([next_label (caar lnfs)])
                   (cons `(define (,l t) (,next_label (cons (list (quote ,next_label) (length t)) t)))
                         (foldr (λ (arg res) (append (Generate-code1 arg static-binders) res)) '() lnfs)
                         ))]
    [`(,l : ,var ,lnfs)
     (if (st-has? static-binders var)
         ;Bvar
         (let ([bind (st-get static-binders var)])
           (let ([m (car bind)]
                 [i (cadr bind)])
             (cons
              `(define (,l t) (CGOTO t ,i))
              (foldr (λ (arg res) (append (Generate-code1 arg static-binders) res)) '() lnfs))
             ))
         ;Fvar
         ;only for arity == 1 !!!!!
         (if (null? lnfs)
             `((define (,l t) (cons 'END-OF-TRAVERSAL t)))
             (let ([new_l (caar lnfs)])
               (cons
                `(define (,l t) (,new_l (cons (list (quote ,new_l) (length t)) t)))
                (Generate-code1 (car lnfs) static-binders))))
             )]
    ))

(define (Generate-code-GOTO1 lnf)
  `((define (CGOTO1 have t p i)
      (if (not (member have ,(cons 'quote `(,(computeFVTokens lnf '())))))
      ,(Generate-code-GOTO1-2 lnf '())
      (cons `EOT t)))))
(define (computeFVTokens lnf bv)
  (match lnf
    ['() '()]
    [`(,l :lambda ,args ,lnfs) (computeFVTokens lnfs (append bv args))]
    [`(,l :@ ,lnfs)
     (foldr (λ (ln res) (append (computeFVTokens ln bv) res)) '() lnfs)]
    [`(,l : ,var ,lnfs)
     (let ([fv (if (member var bv) '() `(,l))])
       (if (null? lnfs)
           fv
           (foldr (λ (ln res) (append (computeFVTokens ln bv) res)) fv lnfs)
       ))]
    ))
(define (Generate-code-GOTO1-2 lnf list)
  (match lnf
    ['() '()]
    [`(,l :lambda ,args ,lnfs)
     (Generate-code-GOTO1-2 lnfs list)]
    [`(,l :@ ,lnfs)
     (let-values ([(len cases)
                   (for/fold ([i 1]
                              [revl '(error 'GOTO:ERROR)])
                             ([el (cdr lnfs)])
                     (let ([point (car el)])
                       (values (+ i 1) `(if (equal? i ,i) (,point (cons (list (quote ,point) p) t)) ,revl))))])
       `(if  (equal? have (quote ,l)) ,cases ,(Generate-code-GOTO1-2 (car lnfs) (append (cdr lnfs) list)))
       )]
    [`(,l : ,var ,lnfs)
     (if (null? lnfs)
         (if (null? list)
             `(error 'ERROR)
             (Generate-code-GOTO1-2 (car list) (cdr list)))
     (let-values ([(len cases)
                   (for/fold ([i 1]
                              [revl '(error 'GOTO:ERROR)])
                             ([el lnfs])
                     (let ([point (car el)])
                       (values (+ i 1) `(if (equal? i ,i) (,point (cons (list (quote ,point) p) t)) ,revl))))])
       `(if  (equal? have (quote ,l)) ,cases ,(Generate-code-GOTO1-2 (car lnfs) (append (cdr lnfs) list)))
       ))]
    ))
(define (Generate-code-auxiliary lnf)
  (append*
   '((define (CGOTO t i)
      (let ((q (- (cadar t) 1)))
        (CGOTO1 (caar (pfx q t)) t q i))))
   (Generate-code-GOTO1 lnf)
   '(((define (FQ have t)
       (letrec ((f (lambda (t0)
                     (if (equal? have (caar t0))
                         (length t0)
                         (let ((bp (cadar t0)))
                           (f (pfx (- bp 1) t)))))))
         (f t))))
     ((define (pfx n t) (reverse (take n (reverse t)))))
     ((define (take n xs) (if (equal? n 0)
                             '()
                             (cons (car xs) (take (- n 1) (cdr xs))))))
     ((define (travout t)
       (if (null? t) '() (begin (travout (cdr t)) (newline) (write (car t))))))
     )))

(Generate-code ongexp+labels)