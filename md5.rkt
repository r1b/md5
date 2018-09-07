#lang r6rs

(library
 (md5)

 (export md5 bytevector->hex-string run-tests)

 (import (rnrs base)
         (rnrs arithmetic bitwise)
         (rnrs arithmetic fixnums)
         (rnrs bytevectors)
         (rnrs lists))

 (define BITS-PER-BYTE 8)
 (define WORD-SIZE-BYTES 4)
 (define DIGEST-SIZE-BYTES (* 4 WORD-SIZE-BYTES))
 (define BLOCK-SIZE-BYTES (* 16 WORD-SIZE-BYTES))
 (define DIGEST-INIT (list #x67452301
                           #xefcdab89
                           #x98badcfe
                           #x10325476))
 (define T (list #xd76aa478 #xe8c7b756 #x242070db #xc1bdceee
                 #xf57c0faf #x4787c62a #xa8304613 #xfd469501
                 #x698098d8 #x8b44f7af #xffff5bb1 #x895cd7be
                 #x6b901122 #xfd987193 #xa679438e #x49b40821
                 #xf61e2562 #xc040b340 #x265e5a51 #xe9b6c7aa
                 #xd62f105d #x02441453 #xd8a1e681 #xe7d3fbc8
                 #x21e1cde6 #xc33707d6 #xf4d50d87 #x455a14ed
                 #xa9e3e905 #xfcefa3f8 #x676f02d9 #x8d2a4c8a
                 #xfffa3942 #x8771f681 #x6d9d6122 #xfde5380c
                 #xa4beea44 #x4bdecfa9 #xf6bb4b60 #xbebfbc70
                 #x289b7ec6 #xeaa127fa #xd4ef3085 #x04881d05
                 #xd9d4d039 #xe6db99e5 #x1fa27cf8 #xc4ac5665
                 #xf4292244 #x432aff97 #xab9423a7 #xfc93a039
                 #x655b59c3 #x8f0ccc92 #xffeff47d #x85845dd1
                 #x6fa87e4f #xfe2ce6e0 #xa3014314 #x4e0811a1
                 #xf7537e82 #xbd3af235 #x2ad7d2bb #xeb86d391))
 
 ; bytevector -> bytevector
 (define (md5 bytes)
   (let* ((padded-bytes (bytevector-append bytes (make-padding bytes)))
          (padded-with-length-bytes (bytevector-append padded-bytes (make-length (bytevector-length bytes)))))
     (make-digest padded-with-length-bytes)))

 ; bytevector -> bytevector
 (define (make-digest message)
   (process-blocks message (bytevector-copy (u32-list->bytevector DIGEST-INIT))))
 
 ; bytevector bytevector -> bytevector
 (define (process-blocks message digest)
   (let ((message-length (bytevector-length message)))
     (if (= message-length 0)
         digest
         (let* ((block (make-bytevector BLOCK-SIZE-BYTES))
                (message-cdr-length (- message-length BLOCK-SIZE-BYTES))
                (message-cdr (make-bytevector message-cdr-length)))
           (begin
             (bytevector-copy! message 0 block 0 BLOCK-SIZE-BYTES)
             (bytevector-copy! message BLOCK-SIZE-BYTES message-cdr 0 message-cdr-length)
             (process-blocks message-cdr (process-block block digest)))))))

 ; bytevector bytevector -> bytevector
 (define (process-block block digest)
   (define TABLE (u32-list->bytevector T))
   ; u32 u32 u32 u32 u8 u8 u8 (u32 u32 u32 -> u32)
   (define (the-operation A B C D block-offset shift-bits table-offset aux-fn)
     (let* ((block-word (bytevector-u32-ref block block-offset 'little))
            (table-word (bytevector-u32-ref TABLE (- table-offset 1) 'little)))
       (u32-sum B (fxrotate-bit-field (u32-sum A (aux-fn B C D) block-word table-word) 0 (* WORD-SIZE-BYTES BITS-PER-BYTE) shift-bits))))
   (let* ((a-offset 0)
          (b-offset 4)
          (c-offset 8)
          (d-offset 12)
          (A (lambda () (bytevector-u32-ref digest a-offset 'little)))
          (B (lambda () (bytevector-u32-ref digest b-offset 'little)))
          (C (lambda () (bytevector-u32-ref digest c-offset 'little)))
          (D (lambda () (bytevector-u32-ref digest d-offset 'little)))
          (AA (A))
          (BB (B))
          (CC (C))
          (DD (D)))
     (begin
       ; round 1
       (bytevector-u32-set! digest a-offset (the-operation (A) (B) (C) (D) 0 7 1 F) 'little)
       (bytevector-u32-set! digest d-offset (the-operation (D) (A) (B) (C) 1 12 2 F) 'little)
       (bytevector-u32-set! digest c-offset (the-operation (C) (D) (A) (B) 2 17 3 F) 'little)
       (bytevector-u32-set! digest b-offset (the-operation (B) (C) (D) (A) 3 22 4 F) 'little)
       (bytevector-u32-set! digest a-offset (the-operation (A) (B) (C) (D) 4 7 5 F) 'little)
       (bytevector-u32-set! digest d-offset (the-operation (D) (A) (B) (C) 5 12 6 F) 'little)
       (bytevector-u32-set! digest c-offset (the-operation (C) (D) (A) (B) 6 17 7 F) 'little)
       (bytevector-u32-set! digest b-offset (the-operation (B) (C) (D) (A) 7 22 8 F) 'little)
       (bytevector-u32-set! digest a-offset (the-operation (A) (B) (C) (D) 8 7 9 F) 'little)
       (bytevector-u32-set! digest d-offset (the-operation (D) (A) (B) (C) 9 12 10 F) 'little)
       (bytevector-u32-set! digest c-offset (the-operation (C) (D) (A) (B) 10 17 11 F) 'little)
       (bytevector-u32-set! digest b-offset (the-operation (B) (C) (D) (A) 11 22 12 F) 'little)
       (bytevector-u32-set! digest a-offset (the-operation (A) (B) (C) (D) 12 7 13 F) 'little)
       (bytevector-u32-set! digest d-offset (the-operation (D) (A) (B) (C) 13 12 14 F) 'little)
       (bytevector-u32-set! digest c-offset (the-operation (C) (D) (A) (B) 14 17 15 F) 'little)
       (bytevector-u32-set! digest b-offset (the-operation (B) (C) (D) (A) 15 22 16 F) 'little)      
       ; round 2
       (bytevector-u32-set! digest a-offset (the-operation (A) (B) (C) (D) 1 5 17 G) 'little)
       (bytevector-u32-set! digest d-offset (the-operation (D) (A) (B) (C) 6 9 18 G) 'little)
       (bytevector-u32-set! digest c-offset (the-operation (C) (D) (A) (B) 11 14 19 G) 'little)
       (bytevector-u32-set! digest b-offset (the-operation (B) (C) (D) (A) 0 20 20 G) 'little)
       (bytevector-u32-set! digest a-offset (the-operation (A) (B) (C) (D) 5 5 21 G) 'little)
       (bytevector-u32-set! digest d-offset (the-operation (D) (A) (B) (C) 10 9 22 G) 'little)
       (bytevector-u32-set! digest c-offset (the-operation (C) (D) (A) (B) 15 14 23 G) 'little)
       (bytevector-u32-set! digest b-offset (the-operation (B) (C) (D) (A) 4 20 24 G) 'little)
       (bytevector-u32-set! digest a-offset (the-operation (A) (B) (C) (D) 9 5 25 G) 'little)
       (bytevector-u32-set! digest d-offset (the-operation (D) (A) (B) (C) 14 9 26 G) 'little)
       (bytevector-u32-set! digest c-offset (the-operation (C) (D) (A) (B) 3 14 27 G) 'little)
       (bytevector-u32-set! digest b-offset (the-operation (B) (C) (D) (A) 8 20 28 G) 'little)
       (bytevector-u32-set! digest a-offset (the-operation (A) (B) (C) (D) 13 5 29 G) 'little)
       (bytevector-u32-set! digest d-offset (the-operation (D) (A) (B) (C) 2 9 30 G) 'little)
       (bytevector-u32-set! digest c-offset (the-operation (C) (D) (A) (B) 7 14 31 G) 'little)
       (bytevector-u32-set! digest b-offset (the-operation (B) (C) (D) (A) 12 20 32 G) 'little)
       ; round 3
       (bytevector-u32-set! digest a-offset (the-operation (A) (B) (C) (D) 5 4 33 H) 'little)
       (bytevector-u32-set! digest d-offset (the-operation (D) (A) (B) (C) 8 11 34 H) 'little)
       (bytevector-u32-set! digest c-offset (the-operation (C) (D) (A) (B) 11 16 35 H) 'little)
       (bytevector-u32-set! digest b-offset (the-operation (B) (C) (D) (A) 14 23 36 H) 'little)
       (bytevector-u32-set! digest a-offset (the-operation (A) (B) (C) (D) 1 4 37 H) 'little)
       (bytevector-u32-set! digest d-offset (the-operation (D) (A) (B) (C) 4 11 38 H) 'little)
       (bytevector-u32-set! digest c-offset (the-operation (C) (D) (A) (B) 7 16 39 H) 'little)
       (bytevector-u32-set! digest b-offset (the-operation (B) (C) (D) (A) 10 23 40 H) 'little)
       (bytevector-u32-set! digest a-offset (the-operation (A) (B) (C) (D) 13 4 41 H) 'little)
       (bytevector-u32-set! digest d-offset (the-operation (D) (A) (B) (C) 0 11 42 H) 'little)
       (bytevector-u32-set! digest c-offset (the-operation (C) (D) (A) (B) 3 16 43 H) 'little)
       (bytevector-u32-set! digest b-offset (the-operation (B) (C) (D) (A) 6 23 44 H) 'little)
       (bytevector-u32-set! digest a-offset (the-operation (A) (B) (C) (D) 9 4 45 H) 'little)
       (bytevector-u32-set! digest d-offset (the-operation (D) (A) (B) (C) 12 11 46 H) 'little)
       (bytevector-u32-set! digest c-offset (the-operation (C) (D) (A) (B) 15 16 47 H) 'little)
       (bytevector-u32-set! digest b-offset (the-operation (B) (C) (D) (A) 2 23 48 H) 'little)
       ; round 4
       (bytevector-u32-set! digest a-offset (the-operation (A) (B) (C) (D) 0 6 49 I) 'little)
       (bytevector-u32-set! digest d-offset (the-operation (D) (A) (B) (C) 7 10 50 I) 'little)
       (bytevector-u32-set! digest c-offset (the-operation (C) (D) (A) (B) 14 15 51 I) 'little)
       (bytevector-u32-set! digest b-offset (the-operation (B) (C) (D) (A) 5 21 52 I) 'little)
       (bytevector-u32-set! digest a-offset (the-operation (A) (B) (C) (D) 12 6 53 I) 'little)
       (bytevector-u32-set! digest d-offset (the-operation (D) (A) (B) (C) 3 10 54 I) 'little)
       (bytevector-u32-set! digest c-offset (the-operation (C) (D) (A) (B) 10 15 55 I) 'little)
       (bytevector-u32-set! digest b-offset (the-operation (B) (C) (D) (A) 1 21 56 I) 'little)
       (bytevector-u32-set! digest a-offset (the-operation (A) (B) (C) (D) 8 6 57 I) 'little)
       (bytevector-u32-set! digest d-offset (the-operation (D) (A) (B) (C) 15 10 58 I) 'little)
       (bytevector-u32-set! digest c-offset (the-operation (C) (D) (A) (B) 6 15 59 I) 'little)
       (bytevector-u32-set! digest b-offset (the-operation (B) (C) (D) (A) 13 21 60 I) 'little)
       (bytevector-u32-set! digest a-offset (the-operation (A) (B) (C) (D) 4 6 61 I) 'little)
       (bytevector-u32-set! digest d-offset (the-operation (D) (A) (B) (C) 11 10 62 I) 'little)
       (bytevector-u32-set! digest c-offset (the-operation (C) (D) (A) (B) 2 15 63 I) 'little)
       (bytevector-u32-set! digest b-offset (the-operation (B) (C) (D) (A) 9 21 64 I) 'little)

       (bytevector-u32-set! digest a-offset (u32-sum (A) AA) 'little)
       (bytevector-u32-set! digest b-offset (u32-sum (B) BB) 'little)
       (bytevector-u32-set! digest c-offset (u32-sum (C) CC) 'little)
       (bytevector-u32-set! digest d-offset (u32-sum (D) DD) 'little)
       
       digest)))

 ; u32 u32 u32 -> u32 
 (define (F X Y Z)
   (bitwise-ior (bitwise-and X Y) (bitwise-and (bitwise-not X) Z)))

 ; u32 u32 u32 -> u32 
 (define (G X Y Z)
   (bitwise-ior (bitwise-and X Z) (bitwise-and Y (bitwise-not Z))))

 ; u32 u32 u32 -> u32
 (define (H X Y Z)
   (bitwise-xor X Y Z))

 ; u32 u32 u32 -> u32
 (define (I X Y Z)
   (bitwise-xor Y (bitwise-ior X (bitwise-not Z))))

 ; integer -> bytevector
 (define (make-length message-length)
   (define (u64->u32-list n)
     (let* ((truncated-n (bitwise-and n #xffffffffffffffff))
            (high-n (bitwise-arithmetic-shift-right (bitwise-and n #xffffffff00000000) (* WORD-SIZE-BYTES BITS-PER-BYTE)))
            (low-n (bitwise-and n #x00000000ffffffff)))
       (list low-n high-n)))
   (u32-list->bytevector (u64->u32-list message-length)))

 ; bytevector -> bytevector
 (define (make-padding message)
   (define TARGET-OFFSET-BYTES 56)
   (define PADDING-CAR 128)
   (let* ((message-offset (mod (bytevector-length message) BLOCK-SIZE-BYTES))
          (padding-length (if (= message-offset TARGET-OFFSET-BYTES)
                              BLOCK-SIZE-BYTES
                              (abs (- message-offset TARGET-OFFSET-BYTES))))
          (padding (make-bytevector padding-length 0)))
     (begin
       (bytevector-u8-set! padding 0 PADDING-CAR)
       padding)))

 (define (test-make-padding)
   ; max padding (length = 0)
   (assert (equal? (make-padding (u8-list->bytevector '()))
                   (u8-list->bytevector '(128 0 0 0 0 0 0 0 0 0 0 0 0 0
                                              0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                              0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                              0 0 0 0 0 0 0 0 0 0 0 0 0 0))))
   ; min padding (length = 55)
   (assert (equal? (make-padding
                    (u8-list->bytevector '(0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                             0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                             0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                             0 0 0 0 0 0 0 0 0 0 0 0 0)))
                   (u8-list->bytevector '(128))))

   ; max padding (length = 56)
   (assert (equal? (make-padding
                    (u8-list->bytevector '(0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                             0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                             0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                             0 0 0 0 0 0 0 0 0 0 0 0 0 0)))
                   (u8-list->bytevector '(128 0 0 0 0 0 0 0 0 0 0 0 0 0
                                              0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                              0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                              0 0 0 0 0 0 0 0 0 0 0 0 0 0)))))
 
 ; bytevector ... -> bytevector
 ; FIXME: Space-efficiency
 (define (bytevector-append . bytevectors)
   (let ((new-bytevector (make-bytevector (fold-left + 0 (map bytevector-length bytevectors)))))
     (define (bytevector-append target-start bytevectors)
       (if (null? bytevectors)
           new-bytevector
           (let* ((current-bytevector (car bytevectors))
                  (current-bytevector-length (bytevector-length current-bytevector)))
             (begin
               (bytevector-copy! current-bytevector 0 new-bytevector target-start current-bytevector-length)
               (bytevector-append (+ target-start current-bytevector-length) (cdr bytevectors))))))
     (bytevector-append 0 bytevectors)))

 (define (test-bytevector-append)
   ; empty list
   (let ((bytevector (make-bytevector 0)))
     (assert (equal? (bytevector-append) bytevector)))

   ; one element
   (let ((bytevector-in (u8-list->bytevector '(0 1 2 3)))
         (bytevector-out (u8-list->bytevector '(0 1 2 3))))
     (assert (equal? (bytevector-append bytevector-in) bytevector-out)))

   ; two elements
   (let ((bytevector-in-a (u8-list->bytevector '(0 1 2 3)))
         (bytevector-in-b (u8-list->bytevector '(4 5 6 7)))
         (bytevector-out (u8-list->bytevector '(0 1 2 3 4 5 6 7))))
     (assert (equal? (bytevector-append bytevector-in-a bytevector-in-b) bytevector-out))))

 ; u32 ... -> u32
 (define (u32-sum . operands)
   (bitwise-and (apply + operands) #xffffffff))

 (define (test-u32-sum)
   ; empty list
   (assert (equal? (u32-sum) 0))

   ; one element
   (assert (equal? (u32-sum 42) 42))

   ; two elements
   (assert (equal? (u32-sum 21 21) 42))
   
   ; three elements
   (assert (equal? (u32-sum 14 14 14) 42))

   ; overflow
   (assert (equal? (u32-sum #xffffffff 2) 1)))

 ; '(u32) -> bytevector
 (define (u32-list->bytevector u32-list)
   (let loop ((bytes (make-bytevector (* (length u32-list) WORD-SIZE-BYTES)))
              (words u32-list)
              (offset 0))
     (if (null? words)
         bytes
         (begin
           (bytevector-u32-set! bytes offset (car words) 'little)
           (loop bytes (cdr words) (+ offset WORD-SIZE-BYTES))))))

 (define (test-u32-list->bytevector)
   ; empty list
   (let ((bytevector (make-bytevector 0)))
     (assert (equal? (u32-list->bytevector '()) bytevector)))

   ; one word
   (let ((bytevector (u8-list->bytevector (list 1 0 0 0))))
     (assert (equal? (u32-list->bytevector '(1)) bytevector)))

   ; two words
   (let ((bytevector (u8-list->bytevector (list 1 0 0 0 2 0 0 0))))
     (assert (equal? (u32-list->bytevector '(1 2)) bytevector))))

 ; bytevector -> string
 (define (bytevector->hex-string bytevector)
   (map (lambda (byte) (number->string byte 16)) (bytevector->u8-list bytevector)))

 (define (test-bytevector->hex-string)
   ; empty bytevector
   (assert (equal? (bytevector->hex-string (make-bytevector 0)) '()))

   ; little endian
   (let ((bytevector (make-bytevector WORD-SIZE-BYTES)))
     (begin
       (bytevector-u32-set! bytevector 0 #x42 'little)
       (assert (equal? (bytevector->hex-string bytevector) (list "42" "0" "0" "0")))))

   ; big endian
   (let ((bytevector (make-bytevector WORD-SIZE-BYTES)))
     (begin
       (bytevector-u32-set! bytevector 0 #xdeadbeef 'big)
       (assert (equal? (bytevector->hex-string bytevector) (list "de" "ad" "be" "ef"))))))

 (define (run-tests)
   (begin
     (test-u32-list->bytevector)
     (test-bytevector->hex-string)
     (test-u32-sum)
     (test-bytevector-append)
     (test-make-padding))))