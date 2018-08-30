#lang r6rs

(library
 (md5)

 (export md5)

 (import (rnrs base)
         (rnrs arithmetic bitwise)
         (rnrs bytevectors)
         (rnrs lists))

 (define ENDIANNESS (native-endianness))
 (define WORD-SIZE-BYTES 4)
 (define BLOCK-SIZE-BYTES (* 16 WORD-SIZE-BYTES))
 (define DIGEST-INIT (list #x01 #x23 #x45 #x67
                           #x89 #xab #xcd #xef
                           #xfe #xdc #xba #x98
                           #x76 #x54 #x32 #x10))
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
   (process-blocks message (u8-list->bytevector DIGEST-INIT)))

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
   ; u32 u32 u32 u32 u8 u8 u8 (u32 u32 u32 -> u32)
   (define (the-operation A B C D block-offset shift-bits table-offset aux-fn)
     (let* ((block-word (bytevector-u32-native-ref block block-offset))
            (table-word (list-ref T (- table-offset 1))))
       (u32-sum B (bitwise-arithmetic-shift-left (u32-sum A (aux-fn B C D)) shift-bits))))
   (let* ((a-offset 0)
          (b-offset 4)
          (c-offset 8)
          (d-offset 12)
          (A (lambda () (bytevector-u32-native-ref digest a-offset)))
          (B (lambda () (bytevector-u32-native-ref digest b-offset)))
          (C (lambda () (bytevector-u32-native-ref digest c-offset)))
          (D (lambda () (bytevector-u32-native-ref digest d-offset)))
          (AA (A))
          (BB (B))
          (CC (C))
          (DD (D)))
     (begin
       ; round 1
       (bytevector-u32-native-set! digest a-offset (the-operation (A) (B) (C) (D) 0 7 1 F))
       (bytevector-u32-native-set! digest d-offset (the-operation (D) (A) (B) (C) 1 12 2 F))
       (bytevector-u32-native-set! digest c-offset (the-operation (C) (D) (A) (B) 2 17 3 F))
       (bytevector-u32-native-set! digest b-offset (the-operation (B) (C) (D) (A) 3 22 4 F))
       (bytevector-u32-native-set! digest a-offset (the-operation (A) (B) (C) (D) 4 7 5 F))
       (bytevector-u32-native-set! digest d-offset (the-operation (D) (A) (B) (C) 5 12 6 F))
       (bytevector-u32-native-set! digest c-offset (the-operation (C) (D) (A) (B) 6 17 7 F))
       (bytevector-u32-native-set! digest b-offset (the-operation (B) (C) (D) (A) 7 22 8 F))
       (bytevector-u32-native-set! digest a-offset (the-operation (A) (B) (C) (D) 8 7 9 F))
       (bytevector-u32-native-set! digest d-offset (the-operation (D) (A) (B) (C) 9 12 10 F))
       (bytevector-u32-native-set! digest c-offset (the-operation (C) (D) (A) (B) 10 17 11 F))
       (bytevector-u32-native-set! digest c-offset (the-operation (C) (D) (A) (B) 11 22 12 F))
       (bytevector-u32-native-set! digest a-offset (the-operation (A) (B) (C) (D) 12 7 13 F))
       (bytevector-u32-native-set! digest d-offset (the-operation (D) (A) (B) (C) 13 12 14 F))
       (bytevector-u32-native-set! digest c-offset (the-operation (C) (D) (A) (B) 14 17 15 F))
       (bytevector-u32-native-set! digest b-offset (the-operation (B) (C) (D) (A) 15 22 16 F))      
       ; round 2
       (bytevector-u32-native-set! digest a-offset (the-operation (A) (B) (C) (D) 1 5 17 G))
       (bytevector-u32-native-set! digest d-offset (the-operation (D) (A) (B) (C) 6 9 18 G))
       (bytevector-u32-native-set! digest c-offset (the-operation (C) (D) (A) (B) 11 14 19 G))
       (bytevector-u32-native-set! digest b-offset (the-operation (B) (C) (D) (A) 0 20 20 G))
       (bytevector-u32-native-set! digest a-offset (the-operation (A) (B) (C) (D) 5 5 21 G))
       (bytevector-u32-native-set! digest d-offset (the-operation (D) (A) (B) (C) 10 9 22 G))
       (bytevector-u32-native-set! digest c-offset (the-operation (C) (D) (A) (B) 15 14 23 G))
       (bytevector-u32-native-set! digest b-offset (the-operation (B) (C) (D) (A) 4 20 24 G))
       (bytevector-u32-native-set! digest a-offset (the-operation (A) (B) (C) (D) 9 5 25 G))
       (bytevector-u32-native-set! digest d-offset (the-operation (D) (A) (B) (C) 14 9 26 G))
       (bytevector-u32-native-set! digest c-offset (the-operation (C) (D) (A) (B) 3 14 27 G))
       (bytevector-u32-native-set! digest c-offset (the-operation (C) (D) (A) (B) 8 20 28 G))
       (bytevector-u32-native-set! digest a-offset (the-operation (A) (B) (C) (D) 13 5 29 G))
       (bytevector-u32-native-set! digest d-offset (the-operation (D) (A) (B) (C) 2 9 30 G))
       (bytevector-u32-native-set! digest c-offset (the-operation (C) (D) (A) (B) 7 14 31 G))
       (bytevector-u32-native-set! digest b-offset (the-operation (B) (C) (D) (A) 12 20 32 G))
       ; round 3
       (bytevector-u32-native-set! digest a-offset (the-operation (A) (B) (C) (D) 5 4 33 H))
       (bytevector-u32-native-set! digest d-offset (the-operation (D) (A) (B) (C) 8 11 34 H))
       (bytevector-u32-native-set! digest c-offset (the-operation (C) (D) (A) (B) 11 16 35 H))
       (bytevector-u32-native-set! digest b-offset (the-operation (B) (C) (D) (A) 14 23 36 H))
       (bytevector-u32-native-set! digest a-offset (the-operation (A) (B) (C) (D) 1 4 37 H))
       (bytevector-u32-native-set! digest d-offset (the-operation (D) (A) (B) (C) 4 11 38 H))
       (bytevector-u32-native-set! digest c-offset (the-operation (C) (D) (A) (B) 7 16 39 H))
       (bytevector-u32-native-set! digest b-offset (the-operation (B) (C) (D) (A) 10 23 40 H))
       (bytevector-u32-native-set! digest a-offset (the-operation (A) (B) (C) (D) 13 4 41 H))
       (bytevector-u32-native-set! digest d-offset (the-operation (D) (A) (B) (C) 0 11 42 H))
       (bytevector-u32-native-set! digest c-offset (the-operation (C) (D) (A) (B) 3 16 43 H))
       (bytevector-u32-native-set! digest c-offset (the-operation (C) (D) (A) (B) 6 23 44 H))
       (bytevector-u32-native-set! digest a-offset (the-operation (A) (B) (C) (D) 9 4 45 H))
       (bytevector-u32-native-set! digest d-offset (the-operation (D) (A) (B) (C) 12 11 46 H))
       (bytevector-u32-native-set! digest c-offset (the-operation (C) (D) (A) (B) 15 16 47 H))
       (bytevector-u32-native-set! digest b-offset (the-operation (B) (C) (D) (A) 2 23 48 H))
       ; round 4
       (bytevector-u32-native-set! digest a-offset (the-operation (A) (B) (C) (D) 0 6 49 I))
       (bytevector-u32-native-set! digest d-offset (the-operation (D) (A) (B) (C) 7 10 50 I))
       (bytevector-u32-native-set! digest c-offset (the-operation (C) (D) (A) (B) 14 15 51 I))
       (bytevector-u32-native-set! digest b-offset (the-operation (B) (C) (D) (A) 5 21 52 I))
       (bytevector-u32-native-set! digest a-offset (the-operation (A) (B) (C) (D) 12 6 53 I))
       (bytevector-u32-native-set! digest d-offset (the-operation (D) (A) (B) (C) 3 10 54 I))
       (bytevector-u32-native-set! digest c-offset (the-operation (C) (D) (A) (B) 10 15 55 I))
       (bytevector-u32-native-set! digest b-offset (the-operation (B) (C) (D) (A) 1 21 56 I))
       (bytevector-u32-native-set! digest a-offset (the-operation (A) (B) (C) (D) 8 6 57 I))
       (bytevector-u32-native-set! digest d-offset (the-operation (D) (A) (B) (C) 15 10 58 I))
       (bytevector-u32-native-set! digest c-offset (the-operation (C) (D) (A) (B) 6 15 59 I))
       (bytevector-u32-native-set! digest c-offset (the-operation (C) (D) (A) (B) 13 21 60 I))
       (bytevector-u32-native-set! digest a-offset (the-operation (A) (B) (C) (D) 4 6 61 I))
       (bytevector-u32-native-set! digest d-offset (the-operation (D) (A) (B) (C) 11 10 62 I))
       (bytevector-u32-native-set! digest c-offset (the-operation (C) (D) (A) (B) 2 15 63 I))
       (bytevector-u32-native-set! digest b-offset (the-operation (B) (C) (D) (A) 9 21 64 I))

       (bytevector-u32-native-set! digest a-offset (u32-sum (A) AA))
       (bytevector-u32-native-set! digest b-offset (u32-sum (B) BB))
       (bytevector-u32-native-set! digest c-offset (u32-sum (C) CC))
       (bytevector-u32-native-set! digest d-offset (u32-sum (D) DD))
       
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

 ; integer -> u64
 (define (make-length message-length)
   (let ((truncated-length (bitwise-and message-length #xffffffffffffffff))
         (truncated-length-bytes (make-bytevector 8)))
     (begin
       (bytevector-u64-native-set! truncated-length-bytes 0 truncated-length)
       truncated-length-bytes)))

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

 ; u32 ... -> u32
 (define (u32-sum . operands)
   (bitwise-and (apply + operands) #xffffffff)))