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

(define (err-on-unbound variable frame)
  (display "Variable ")
  (display variable)
  (display " is unbound in frame ")
  (display frame)
  (display "\n")
  false)


(define frame
  (extend '(? x) '(? y)
          (extend '(? y) '(a b) '())))

(binding-in-frame '(? y) frame)
;; ((? y) a b)

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

(instantiate '(p (? x) (? missing))
             frame
             (lambda (v f) v))
;; (p (a b) (? missing))


(define frames
  (cons-stream frame
               (singleton-stream
                (extend '(? x) 'c '()))))

(define answers
  (stream-map
   (lambda (f)
     (instantiate '(p (? x)) f (lambda (v f) v)))
   frames))

(list (stream-ref answers 0)
      (stream-ref answers 1))
;; ((p (a b)) (p c))
