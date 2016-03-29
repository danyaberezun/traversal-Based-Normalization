#lang racket

; =============================
; COMPILER: into low-level code
; (only for o->o case)
; =============================

(define ongexp+labels
'(A :lambda
  ()
  (B :@
   ((C :lambda
     (h z)
     (D : h
      ((E :lambda
       (x)
       (F : h
        ((G :lambda (x1) (H : x ()))
         (I :lambda () (J : a ())))))
       (K :lambda
        ()
        (L : z
         ((M :lambda
          ()
          (N : a ()))))))))
    (O :lambda
     (f y)
     (P : f
      ((Q :lambda
        ()
        (R : g
         ((S :lambda
           ()
           (T : y ()))))))))
    (U :lambda
     (w)
     (V : g ((W :lambda
            ()
            (X : w ()))))))))
  )

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
  `((define (CGOTO1 have t p i) ,(Generate-code-GOTO1-2 lnf st-empty '()))))
(define (Generate-code-GOTO1-2 lnf static-binders list)
  (match lnf
    ['() '()]
    [`(,l :lambda ,args ,lnfs)
     (for-each (λ (arg) (set! static-binders (st-set static-binders arg `(,l ,(get-index args arg))))) args)
     (Generate-code-GOTO1-2 lnfs static-binders list)]
    [`(,l :@ ,lnfs)
     (let-values ([(len cases)
                   (for/fold ([i 1]
                              [revl '(error 'GOTO:ERROR)])
                             ([el (cdr lnfs)])
                     (let ([point (car el)])
                       (values (+ i 1) `(if (equal? i ,i) (,point (cons (list (quote ,point) p) t)) ,revl))))])
       `(if  (equal? have (quote ,l)) ,cases ,(Generate-code-GOTO1-2 (car lnfs) static-binders (append (cdr lnfs) list)))
       )]
    [`(,l : ,var ,lnfs)
     (if (null? lnfs)
         (if (null? list)
             `(error 'ERROR)
             (Generate-code-GOTO1-2 (car list) static-binders (cdr list)))
     (let-values ([(len cases)
                   (for/fold ([i 1]
                              [revl '(error 'GOTO:ERROR)])
                             ([el lnfs])
                     (let ([point (car el)])
                       (values (+ i 1) `(if (equal? i ,i) (,point (cons (list (quote ,point) p) t)) ,revl))))])
       `(if  (equal? have (quote ,l)) ,cases ,(Generate-code-GOTO1-2 (car lnfs) static-binders (append (cdr lnfs) list)))
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