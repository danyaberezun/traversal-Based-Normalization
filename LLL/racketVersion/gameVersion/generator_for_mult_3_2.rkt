#lang racket

;===============================
; program tree for function mult
;===============================
(define mult
'(A :lambda ()
  (B :@
   ((C :lambda (m n s z)
     (D : m
      ((E :lambda (a)
       (F : n
        ((G :lambda (b) (H : s ((I :lambda () (J : b ())))))
         (K :lambda () (L : a ())))))
       (M :lambda () (N : z ())))))
    (O :data 1)
    (W :data 2)
    (AC :lambda (e) (AD : t ((AE :lambda () (AF : e ())))))
    (AG :lambda () (AH : y ()))
    )))
  )

;=========================
; data tree for data three
;=========================
(define three
'(O :lambda (f c)
    (P : f ((Q :lambda () (R : f ((S :lambda () (T : f ((U :lambda () (V : c ()))))))))))))

;=======================
; data tree for data two
;=======================
(define two
  '(W :lambda (g v) (X : g ((Y :lambda () (Z : g ((AA :lambda () (AB : v ())))))))))


(define (get-index l i)
  (match l
    [`(,x . ,y) (if (equal? x i) 1 (+ 1 (get-index y i)))]
    [`() (error "get-index: empty list")]))

(define st-get dict-ref)
(define st-has? dict-has-key?)
(define st-set dict-set)
(define st-empty  #hash())

;====================================================================
; fucntion Generate-program generates low-level code for program part
; lnf is a annotated long form of program part
;====================================================================
(define (Generate-program lnf)
  (append (Generate-code-GOTO1 lnf 0) (Generate-code-auxiliary lnf (compute-data-number lnf))
          (Generate-code1 lnf st-empty) `((reverse (,(car lnf) (quote ((,(car lnf), 0))))))))

(define (compute-data-number lnf)
  (match lnf
    [`(,l :data ,i) 1]
    [`(,l :lambda ,args ,lnf)
     (compute-data-number lnf)]
    [`(,l :@ ,lnfs)
     (foldl (λ (lnf acc1)
              (match lnf
                [`(,bi :lambda ,args ,nn)
                 (+ acc1 (compute-data-number nn))]
                [`(,ll :data ,nn) (+ acc1 1)])) 0 lnfs)]
    [`(,l : ,var ,lnfs)
     (foldl (λ (lnf acc1)
              (match lnf
                [`(,bi :lambda ,args ,nn)
                 (+ acc1 (compute-data-number nn))]
                [`(,ll :data ,nn) (+ acc1 1)])) 0 lnfs)]
     ))

(define (Generate-data lnf number)
  (append (Generate-code-GOTO1 lnf number) (Generate-code1 lnf st-empty)))

(define (get-ith l i)
  (if (equal? i 1)
      (car l)
      (get-ith (cdr l) (- i 1))))

(define (Generate-code1 lnf static-binders)
  (match lnf
    [`(,l :data ,i) `()]
    [`(,l :lambda ,args ,lnf)
     (set! static-binders
           (foldl (λ (arg acc)
                    (if (st-has? acc arg)
                        acc
                        (st-set acc arg `(,l ,(get-index args arg) ?))))
                  static-binders args))
     (match lnf
       [`(,ln :@ ,As) (cons `(define (,l t) (,ln (cons (list (quote ,ln) 0) t)))
                            (Generate-code1 lnf static-binders))]
       [`(,ln : ,var ,As)
        (if (st-has? static-binders var)
            (let ([bind (st-get static-binders var)])
              (cons `(define (,l t) (,ln (cons (list (quote ,ln) (FQ (quote ,(car bind)) t)) t)))
                    (Generate-code1 lnf static-binders)))
            (cons `(define (,l t) (,ln (cons (list (quote ,ln) 1) t)))
                  (Generate-code1 lnf static-binders)))]
       )]
    [`(,l :@ ,lnfs)
     (match (car lnfs)
       [`(,bi :lambda ,args ,bs)
        (set! static-binders
              (foldl (λ (arg acc) (st-set acc arg
                                          (let ([i (get-index args arg)])
                                            `(,bi ,i ,(get-ith lnfs (+ i 1))))))
                     static-binders args))])
     (set! static-binders
           (foldl (λ (lnf acc1)
                    (match lnf
                      [`(,bi :lambda ,args ,nn)
                       (foldl (λ (arg acc)
                                (st-set acc arg `(,bi ,(get-index args arg) ?))) acc1 args)]
                      [`(,ll :data ,nn) acc1])) static-binders (cdr lnfs)))
     (let ([next_label (caar lnfs)])
       (cons `(define (,l t) (,next_label (cons (list (quote ,next_label) (length t)) t)))
             (foldr (λ (arg res) (append (Generate-code1 arg static-binders) res)) '() lnfs)
             ))]
    [`(,l : ,var ,lnfs)
     (set! static-binders
           (foldl (λ (lnf acc1)
                    (match lnf
                      [`(,bi :lambda ,args ,nn)
                       (foldl (λ (arg acc)
                                (st-set acc arg `(,bi ,(get-index args arg) ?))) acc1 args)]
                      [`(,ll :data ,nn) acc1])) static-binders lnfs))
     (if (st-has? static-binders var)
         ;Bvar
         (let ([bind (st-get static-binders var)])
           (let ([bi_l (car bind)]
                 [i    (cadr bind)]
                 [bi_e (caddr bind)])
             (match bi_e
               ; Bvar with statically unknown next point
               ['? (cons
                      `(define (,l t) (CGOTO t ,i))
                      (foldr (λ (arg res) (append (Generate-code1 arg static-binders) res)) '()
                             lnfs))]
               ; Bvar with statically known DATA as next
               [`(,n_l :data ,n_i)
                (cons
                 `(define (,l t) (CGOTO t ,i))
                 (foldr (λ (arg res) (append (Generate-code1 arg static-binders) res)) '() lnfs))]
               ; Bvar with statically known next point
               [`,next
                #;(cons
                   `(define (,l t) (cons (list (quote ,(car next)) (FQ (quote ,(car next)) t)))
                      (- (cadar t) 1))
                   (foldr (λ (arg res) (append (Generate-code1 arg static-binders) res)) '() lnfs))
                (cons
                 `(define (,l t) (CGOTO t ,i))
                 (foldr (λ (arg res) (append (Generate-code1 arg static-binders) res)) '() lnfs))]
               )))
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

(define (Generate-code-GOTO1 lnf number)
  `((define (,(string->symbol (string-append "CGOTO_" (number->string number))) have t p i)
      ,(Generate-code-GOTO1-2 lnf st-empty '()))))
(define (Generate-code-GOTO1-2 lnf static-binders list)
  (match lnf
    ['() '()]
    [`(,l :lambda ,args ,lnfs)
     (for-each (λ (arg) (set! static-binders (st-set static-binders arg `(,l ,(get-index args arg)))))
               args)
     (Generate-code-GOTO1-2 lnfs static-binders list)]
    [`(,l :@ ,lnfs)
     (let-values ([(len cases)
                   (for/fold ([i 1]
                              [revl '(error 'GOTO:ERROR)])
                             ([el (cdr lnfs)])
                     (let ([point (car el)])
                       (values (+ i 1) `(if (equal? i ,i) (,point (cons (list (quote ,point) p) t))
                                            ,revl))))])
       `(if  (equal? have (quote ,l)) ,cases ,(Generate-code-GOTO1-2 (car lnfs) static-binders
                                                                     (append (cdr lnfs) list)))
       )]
    [`(,l : ,var ,lnfs)
     (if (null? lnfs)
         (if (null? list)
             ''ERROR
             (Generate-code-GOTO1-2 (car list) static-binders (cdr list)))
         (let-values ([(len cases)
                       (for/fold ([i 1]
                                  [revl '(error 'GOTO:ERROR)])
                                 ([el lnfs])
                         (let ([point (car el)])
                           (values (+ i 1) `(if (equal? i ,i)
                                                (,point (cons (list (quote ,point) p) t))
                                                ,revl))))])
           `(if  (equal? have (quote ,l)) ,cases ,(Generate-code-GOTO1-2 (car lnfs) static-binders
                                                                         (append (cdr lnfs) list)))
           ))]
    [`(,l :data ,i)
     (Generate-code-GOTO1-2 (car list) static-binders (cdr list))]
    ))

(define (gen-list data_number)
  (if (equal? data_number 0)
      '()
      `(data_number ,(gen-list (- data_number 1)))))
(define (generate-CGOTO-common1 data_number)
  (if (equal? data_number 0)
      `(let ([res (CGOTO_0 have t p i)])
          (if (not (equal? res 'ERROR))
              res
              'ERROR))
      `(let ([res (,(string->symbol (string-append "CGOTO_" (number->string data_number)))
                   have t p i)])
          (if (not (equal? res 'ERROR))
              res
              ,(generate-CGOTO-common1 (- data_number 1))))
      ))
(define (generate-CGOTO-common data_number)
  `((define (CGOTO_common have t p i)
      ,(generate-CGOTO-common1 data_number)
   )))

;=====================================================================================
; function Generate-code-auxiliary generates an auxiliary fucntion that are common for
;   data part and program part
; data_number is a count of data in program part
;=====================================================================================
(define (Generate-code-auxiliary lnf data_number)
  (append*
   '((define (CGOTO t i)
      (let ((q (- (cadar t) 1)))
        (CGOTO_common (caar (pfx q t)) t q i))))
   (generate-CGOTO-common data_number)
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

;================================================================================
; (Generate-data three 1) generates code for first data i.e. Church numeral three
; (Generate-data two   2) generates code for second data i.e. Church numeral  two
; (Generate-program mult) generates code for program 'mult'
;================================================================================
(append (Generate-data three 1) (Generate-data two 2) (Generate-program mult))