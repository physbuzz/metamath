#lang sicp

(define (stream-car stream) (car stream))
(define (stream-cdr stream) (force (cdr stream)))
(define (singleton-stream x)
        (cons-stream x the-empty-stream))

(define (integers-starting-from n) (cons-stream n (integers-starting-from (+ n 1))))
(define (stream-ref s n) 
        (if (<= n 0)
            (stream-car s)
            (stream-ref (stream-cdr s) (- n 1))))


(define (stream-map proc s)
  (if (stream-null? s)
      the-empty-stream
      (cons-stream (proc (stream-car s))
                   (stream-map proc (stream-cdr s)))))

(define (stream-filter pred s)
  (cond ((stream-null? s) the-empty-stream)
        ((pred (stream-car s))
         (cons-stream (stream-car s)
                      (stream-filter pred (stream-cdr s))))
        (else
         (stream-filter pred (stream-cdr s)))))

(define integers (integers-starting-from 1))

(stream-ref integers 9)
;; 10

(stream-ref
 (stream-map (lambda (x) (* x x)) integers)
 4)
;; 25

(stream-ref (stream-filter even? integers) 4)
;; 10

(stream-null?
 (stream-cdr
  (stream-map (lambda (x) (* x x))
              (singleton-stream 3))))
;; #t

(stream-null?
 (stream-filter even? (singleton-stream 3)))
;; #t
