#lang racket/base
(require data/gvector
         rackunit)

;; Multi-threaded stress tests for gvector memory safety.
;; Tests both regular threads (concurrent access) and parallel
;; threads (using #:pool for true parallelism).
;;
;; The primary goal is memory safety: no crashes or segfaults.
;; Count correctness is checked for non-parallel (coroutine) threads
;; where operations are interleaved but not truly concurrent.
;; For parallel threads, count may be incorrect due to races on the
;; n field, but operations must not cause memory-unsafe behavior.

(define ITEMS-PER-THREAD 1000)
(define NUM-THREADS 8)

;; Test 1: Concurrent adds from multiple coroutine threads
(test-case "concurrent gvector-add!"
  (for ([_ (in-range 10)])
    (define gv (make-gvector))
    (define threads
      (for/list ([t (in-range NUM-THREADS)])
        (thread (lambda ()
                  (for ([i (in-range ITEMS-PER-THREAD)])
                    (gvector-add! gv i))))))
    (for-each thread-wait threads)
    (check-equal? (gvector-count gv) (* NUM-THREADS ITEMS-PER-THREAD))))

;; Test 2: Parallel adds — tests memory safety, not count correctness
(test-case "parallel gvector-add!"
  (for ([_ (in-range 10)])
    (define gv (make-gvector))
    (define pool (make-parallel-thread-pool NUM-THREADS))
    (define threads
      (for/list ([t (in-range NUM-THREADS)])
        (thread #:pool pool
                (lambda ()
                  (for ([i (in-range ITEMS-PER-THREAD)])
                    (gvector-add! gv i))))))
    (parallel-thread-pool-close pool)
    (for-each thread-wait threads)
    ;; Count may be less than expected due to n-field races,
    ;; but we should not crash
    (check-true (> (gvector-count gv) 0))))

;; Test 3: Concurrent reads while adding
(test-case "concurrent add + ref"
  (for ([_ (in-range 10)])
    (define gv (make-gvector))
    (define stop? #f)
    (define writers
      (for/list ([t (in-range 4)])
        (thread (lambda ()
                  (for ([i (in-range ITEMS-PER-THREAD)])
                    (gvector-add! gv i))))))
    ;; Reader threads - should never crash even with stale data
    (define readers
      (for/list ([t (in-range 4)])
        (thread (lambda ()
                  (let loop ()
                    (define n (gvector-count gv))
                    (when (> n 0)
                      (gvector-ref gv (sub1 n) #f))
                    (unless stop?
                      (loop)))))))
    (for-each thread-wait writers)
    (set! stop? #t)
    (for-each thread-wait readers)
    (check-equal? (gvector-count gv) (* 4 ITEMS-PER-THREAD))))

;; Test 4: Parallel reads while adding — the key memory safety test.
;; Without vec-before-n ordering, this can segfault when a concurrent
;; remove shrinks the vector between reading n and reading vec.
(test-case "parallel add + ref"
  (for ([_ (in-range 10)])
    (define gv (make-gvector))
    (define stop? #f)
    (define pool (make-parallel-thread-pool 8))
    (define writers
      (for/list ([t (in-range 4)])
        (thread #:pool pool
                (lambda ()
                  (for ([i (in-range ITEMS-PER-THREAD)])
                    (gvector-add! gv i))))))
    (define readers
      (for/list ([t (in-range 4)])
        (thread #:pool pool
                (lambda ()
                  (let loop ()
                    (define n (gvector-count gv))
                    (when (> n 0)
                      (gvector-ref gv (sub1 n) #f))
                    (unless stop?
                      (loop)))))))
    (parallel-thread-pool-close pool)
    (for-each thread-wait writers)
    (set! stop? #t)
    (for-each thread-wait readers)))

;; Test 5: Concurrent iteration while adding
(test-case "concurrent add + in-gvector"
  (for ([_ (in-range 10)])
    (define gv (make-gvector))
    (define stop? #f)
    (define writers
      (for/list ([t (in-range 4)])
        (thread (lambda ()
                  (for ([i (in-range ITEMS-PER-THREAD)])
                    (gvector-add! gv i))))))
    (define readers
      (for/list ([t (in-range 4)])
        (thread (lambda ()
                  (let loop ()
                    (for ([x (in-gvector gv)])
                      (void))
                    (unless stop?
                      (loop)))))))
    (for-each thread-wait writers)
    (set! stop? #t)
    (for-each thread-wait readers)))

;; Test 6: Parallel iteration while adding
(test-case "parallel add + in-gvector"
  (for ([_ (in-range 10)])
    (define gv (make-gvector))
    (define stop? #f)
    (define pool (make-parallel-thread-pool 8))
    (define writers
      (for/list ([t (in-range 4)])
        (thread #:pool pool
                (lambda ()
                  (for ([i (in-range ITEMS-PER-THREAD)])
                    (gvector-add! gv i))))))
    (define readers
      (for/list ([t (in-range 4)])
        (thread #:pool pool
                (lambda ()
                  (let loop ()
                    (for ([x (in-gvector gv)])
                      (void))
                    (unless stop?
                      (loop)))))))
    (parallel-thread-pool-close pool)
    (for-each thread-wait writers)
    (set! stop? #t)
    (for-each thread-wait readers)))

;; Test 7: Concurrent add + remove-last!
(test-case "concurrent add + remove-last!"
  (for ([_ (in-range 10)])
    (define gv (make-gvector))
    (for ([i (in-range 100)])
      (gvector-add! gv i))
    (define writers
      (for/list ([t (in-range 4)])
        (thread (lambda ()
                  (for ([i (in-range ITEMS-PER-THREAD)])
                    (gvector-add! gv i))))))
    (define removers
      (for/list ([t (in-range 2)])
        (thread (lambda ()
                  (let loop ([removed 0])
                    (when (< removed 100)
                      (with-handlers ([exn:fail? (lambda (e) (loop removed))])
                        (gvector-remove-last! gv)
                        (loop (add1 removed)))))))))
    (for-each thread-wait writers)
    (for-each thread-wait removers)))

;; Test 8: Parallel add + remove — the key race condition test.
;; Without vec-before-n ordering in gvector-ref, a remove that shrinks
;; the backing vector can cause an out-of-bounds unsafe-vector*-ref.
(test-case "parallel add + remove-last!"
  (for ([_ (in-range 10)])
    (define gv (make-gvector))
    (for ([i (in-range 100)])
      (gvector-add! gv i))
    (define pool (make-parallel-thread-pool 6))
    (define writers
      (for/list ([t (in-range 4)])
        (thread #:pool pool
                (lambda ()
                  (for ([i (in-range ITEMS-PER-THREAD)])
                    (gvector-add! gv i))))))
    (define removers
      (for/list ([t (in-range 2)])
        (thread #:pool pool
                (lambda ()
                  (let loop ([removed 0])
                    (when (< removed 100)
                      (with-handlers ([exn:fail? (lambda (e) (loop removed))])
                        (gvector-remove-last! gv)
                        (loop (add1 removed)))))))))
    (parallel-thread-pool-close pool)
    (for-each thread-wait writers)
    (for-each thread-wait removers)))

;; Test 9: Concurrent gvector-set!
(test-case "concurrent gvector-set!"
  (for ([_ (in-range 10)])
    (define gv (make-gvector))
    (for ([i (in-range 100)])
      (gvector-add! gv i))
    (define threads
      (for/list ([t (in-range NUM-THREADS)])
        (thread (lambda ()
                  (for ([i (in-range ITEMS-PER-THREAD)])
                    (gvector-set! gv (modulo i 100) i))))))
    (for-each thread-wait threads)
    (check-equal? (gvector-count gv) 100)))

;; Test 10: Parallel gvector-set!
(test-case "parallel gvector-set!"
  (for ([_ (in-range 10)])
    (define gv (make-gvector))
    (for ([i (in-range 100)])
      (gvector-add! gv i))
    (define pool (make-parallel-thread-pool NUM-THREADS))
    (define threads
      (for/list ([t (in-range NUM-THREADS)])
        (thread #:pool pool
                (lambda ()
                  (for ([i (in-range ITEMS-PER-THREAD)])
                    (gvector-set! gv (modulo i 100) i))))))
    (parallel-thread-pool-close pool)
    (for-each thread-wait threads)
    (check-equal? (gvector-count gv) 100)))

;; Test 11: for/gvector correctness under concurrency
(test-case "for/gvector concurrent correctness"
  (for ([_ (in-range 10)])
    (define ch (make-channel))
    (define threads
      (for/list ([t (in-range NUM-THREADS)])
        (thread (lambda ()
                  (define gv (for/gvector ([i (in-range ITEMS-PER-THREAD)]) i))
                  (channel-put ch gv)))))
    (for ([_ (in-range NUM-THREADS)])
      (define gv (channel-get ch))
      (check-equal? (gvector-count gv) ITEMS-PER-THREAD))))

;; Test 12: Parallel read + remove stress — specifically targets the
;; vec-before-n ordering bug. Readers continuously read the last element
;; while removers shrink the vector, which can trigger the race where
;; n is read before vec, and vec gets replaced with a shorter one.
;; We fill with many elements then remove most of them to trigger trim!
;; which replaces vec with a shorter vector.
(test-case "parallel ref + remove stress"
  (for ([_ (in-range 50)])
    (define gv (make-gvector))
    ;; Fill with enough elements that removing most will trigger trim!
    ;; trim! fires when cap >= 4*n, so removing 400 of 500 leaves n=100
    ;; with cap=512 (or similar), triggering shrink to 256, still safe.
    ;; But if we keep removing down to n=10 with cap=256, trim! shrinks
    ;; to 128, then 64, etc. During any shrink, the vec is replaced.
    (for ([i (in-range 1000)])
      (gvector-add! gv i))
    (define pool (make-parallel-thread-pool 8))
    ;; Readers that aggressively read near the end of the gvector
    (define readers
      (for/list ([t (in-range 4)])
        (thread #:pool pool
                (lambda ()
                  (for ([_ (in-range 50000)])
                    (define n (gvector-count gv))
                    (when (> n 0)
                      ;; Access near the end where trim! is most dangerous
                      (gvector-ref gv (sub1 n) #f)))))))
    ;; Removers that aggressively shrink the gvector
    (define removers
      (for/list ([t (in-range 4)])
        (thread #:pool pool
                (lambda ()
                  (for ([_ (in-range 200)])
                    (with-handlers ([exn:fail? void])
                      (gvector-remove-last! gv)))))))
    (parallel-thread-pool-close pool)
    (for-each thread-wait readers)
    (for-each thread-wait removers)))
