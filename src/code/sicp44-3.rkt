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
         (pattern-match dat (cdr l) frame)
         ; Else, var is free for us to define.
         (extend var dat frame))))
(define (pattern-match pat dat frame)
  (cond ((var? pat) (extend-if-consistent pat dat frame))
        ((and (pair? pat) (pair? dat)) 
          (let ((nf (pattern-match (car pat) (car dat) frame)))
               (if (eq? nf 'failed) 
                   'failed
                   (pattern-match (cdr pat) (cdr dat) nf))))
        ((eq? pat dat) frame)
        (else 'failed)))



(pattern-match '(p (? x) (? x))
               '(p a a)
               '())
;; (((? x) . a))

(pattern-match '(p (? x) (? x))
               '(p a b)
               '())
;; failed

(pattern-match '(a . (? rest))
               '(a b c)
               '())
;; (((? rest) b c))
