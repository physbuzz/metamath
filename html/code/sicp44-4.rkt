#lang sicp

(define (stream-car stream) (car stream))
(define (stream-cdr stream) (force (cdr stream)))
(define (singleton-stream x)
        (cons-stream x the-empty-stream))
(define (stream-map proc s)
  (if (stream-null? s)
      the-empty-stream
      (cons-stream (proc (stream-car s))
                   (stream-map proc (stream-cdr s)))))
(define (stream-ref s n) 
        (if (<= n 0)
            (stream-car s)
            (stream-ref (stream-cdr s) (- n 1))))

(define (make-binding variable value)
  (cons variable value))
(define (binding-variable binding) (car binding))
(define (binding-value binding) (cdr binding))
(define (binding-in-frame variable frame)
  (assoc variable frame))
(define (extend variable value frame)
  (cons (make-binding variable value) frame))
(define (tagged-list? exp tag)
  (if (pair? exp) (eq? (car exp) tag) false))
(define (var? exp)
  (tagged-list? exp '?))

; Apply the substitutions in "frame" to "expression". This is a bit like
; the Mathematica "ReplaceRepeated" or "//." operation.
(define (instantiate exp frame unbound-var-handler)
  (cond ((var? exp) 
         (let ((res (assoc exp frame)))
              (if res 
                (instantiate (cdr res) frame unbound-var-handler)
                (unbound-var-handler exp frame))))
        ((pair? exp) 
         (cons 
           (instantiate (car exp) frame unbound-var-handler)
           (instantiate (cdr exp) frame unbound-var-handler)))
         (else exp)))

(define (extend-if-consistent var dat frame)
  (let ((l (assoc var frame)))
       (if l 
         ; If it's defined, the data has to be consistent with the matched variable
         (pattern-match (cdr l) dat frame)
         ; Else, var is free for us to define.
         (extend var dat frame))))
(define (pattern-match pat dat frame)
  (cond ((eq? frame 'failed) 'failed)
        ((var? pat) (extend-if-consistent pat dat frame))
        ((and (pair? pat) (pair? dat)) 
          (let ((nf (pattern-match (car pat) (car dat) frame)))
               (if (eq? nf 'failed) 
                   'failed
                   (pattern-match (cdr pat) (cdr dat) nf))))
        ((equal? pat dat) frame)
        (else 'failed)))


(define (extend-if-possible var val frame)
  (let ((existing (binding-in-frame var frame)))
    (cond
      (existing
       (unify-match (binding-value existing) val frame))

      ((var? val)
       (let ((other (binding-in-frame val frame)))
         (if other
             (unify-match var (binding-value other) frame)
             (extend var val frame))))

      ((depends-on? val var frame)
       'failed)

      (else
       (extend var val frame)))))
(define (unify-match p1 p2 frame)
  (cond ((eq? frame 'failed) 'failed)
    ((equal? p1 p2) frame)
    ((var? p1) (extend-if-possible p1 p2 frame))
    ((var? p2) (extend-if-possible p2 p1 frame))
    ((and (pair? p1) (pair? p2))
     (unify-match
       (cdr p1)
       (cdr p2)
       (unify-match (car p1) (car p2) frame)))
    (else 'failed)))

(define (depends-on? exp var frame)
  (cond
    ((var? exp)
     (or (equal? exp var)
         (let ((binding (binding-in-frame exp frame)))
           (and binding
                (depends-on?
                  (binding-value binding)
                  var
                  frame)))))
    ((pair? exp)
     (or (depends-on? (car exp) var frame)
         (depends-on? (cdr exp) var frame)))
    (else false)))

(unify-match '(p (? x) (? y))
             '(p (? y) (? x))
             '())
;; (((? x) ? y))
(define unified
  (unify-match '(p (? x) (? y))
               '(p (f (? y)) 3)
               '()))

(instantiate '(? x) unified (lambda (v f) v))
;; (f 3)
(unify-match '(? y)
             '(f (? x))
             (extend '(? x) '(? y) '()))
;; failed
