(in-package "ACL2S")

(modeling-start)
;(modeling-validate-defs)
;(modeling-admit-defs)
;(modeling-admit-all)
#|

Utility functions

|#


;; TODO: prove that we can access map like alist
(definec map-keys (m :all) :tl
     :input-contract (good-map m)
     (if (endp m)
         '()
         (cons (caar m) (map-keys (cdr m)))))

(definec map-values (m :all) :tl
     :input-contract (good-map m)
     (if (endp m)
         '()
         (cons (cdar m) (map-values (cdr m)))))

(definec contains-keys (k :tl m :all) :bool
     :input-contract (good-map m)
     (if (lendp k)
         t
         (and (mget (first k) m)
          (contains-keys (rest k) m))))

(definec is-prefix (test :tl base :tl) :bool
     (match (list test base)
         (('() &) t)
       (((& . &) '()) nil)
       (((f1 . r1) (f2 . r2))
        (and (== f1 f2)
         (is-prefix r1 r2)))))

(definec is-suffix (test :tl base :tl) :bool
     (is-prefix (reverse test) (reverse base)))

(defdata lor (listof rational))
(definec less-than-all (v :rational l :lor) :bool
     (if (lendp l)
         t
         (and (< v (first l))
          (less-than-all v (rest l)))))

(defdata none 'none)

#|

Replica defdatas

|#

(defdata value-type int)
(defdata addr-comp (range integer (0 <= _ < 256)))
(defdata address (list addr-comp addr-comp addr-comp addr-comp))
(defdata loaddr (listof address))
(defdata soaddr (map address integer)) ;; use map to bool as lazy set

(defdata replica-role (enum '(PRIMARY BACKUP)))
(defdata replica-data (listof value-type))
(defdata replica-buffer (map nat value-type))
(defdata replica (record
          (addr . address)
          (role . replica-role)
          (data . replica-data) ;; store committed data
          (buffer . replica-buffer) ;; store out-of-order updates
          (backups . soaddr)))

(defdata replica-group (map address replica))
(defdata lorep (listof replica))

#|

Replica initialization functions

|#

;; Initialize replica.
(definec init-replica (addr :address role :replica-role backups :soaddr) :replica
     :function-contract-hints (("Goal" :in-theory (disable addressp replica))
                   ("Subgoal 1'" :use ((:instance replica-constructor-pred
                                 (replica-addr addr)
                                 (replica-role role)
                                 (replica-data '())
                                 (replica-buffer '())
                                 (replica-backups backups)))))

     :input-contract (and (! (mget addr backups)))
     (replica addr role '() '() backups))


(definec init-replica-group-helper (addrs :loaddr primary :address backups :soaddr) :replica-group
     :input-contract (and
              (! (mget primary backups))
              (contains-keys addrs backups))
     (if (lendp addrs)
             (mset primary (init-replica primary 'PRIMARY backups) '())
             (mset (car addrs) (init-replica (car addrs) 'BACKUP '())
                   (init-replica-group-helper (rest addrs) primary backups))))

;; Initialize replica group.
(definec init-replica-group (primary :address backups :soaddr) :replica-group
     :input-contract (! (mget primary backups))
     (init-replica-group-helper (map-keys backups) primary backups))

#|

Replica utility functions

|#
(definec primaryp (r :replica) :bool
  (== 'PRIMARY (mget :role r)))

(definec num-primaries-helper (rg :lorep) :nat
     (if (lendp rg)
         0
         (+ (if (primaryp (first rg)) 1 0)
        (num-primaries-helper (rest rg)))))

(definec num-primaries (rg :replica-group) :nat
     (num-primaries-helper (map-values rg)))

(definec get-primary-helper (rg :lorep) :replica
     :input-contract (and
              (! (lendp rg))
              (= 1 (num-primaries-helper rg)))
     (if (primaryp (first rg))
         (first rg)
         (get-primary-helper (rest rg))))

(definec get-primary (rg :replica-group) :replica
     :input-contract (and
              (! (endp rg))
              (= 1 (num-primaries rg)))
     (get-primary-helper (map-values rg)))


(definec get-backups (rg :replica-group) :lorep
     (if (endp rg)
         '()
         (if (! (primaryp (cdar rg)))
         (cons (cdar rg) (get-backups (cdr rg)))
         (get-backups (cdr rg)))))

#|

Replica validity predicate

|#

;; Returns t if replica state is valid. Nil otherwise.
(definec valid-replica (r :replica) :bool
     (and
      ;; :backups stores only writes received out-of-order
      (let ((next-idx (llen (mget :data r)))
        (buffered-indices (map-keys (mget :buffer r))))
        (less-than-all next-idx buffered-indices))
      ;; current replica :addr is not in :backups.
      (! (mget (mget :addr r) (mget :backups r)))
      ;; backups have empty :backups member
      (=> (== 'BACKUP (mget :role r))
          (zp (len (mget :backups r))))
      ;; primaries have empty :buffer member
      (=> (== 'PRIMARY (mget :buffer r))
          (zp (len (mget :buffer r))))))

(definec valid-replicas (rg :replica-group) :bool
     (if (endp rg)
         t
         (and (valid-replica (cdar rg))
          (valid-replicas (cdr rg)))))

(definec valid-replica-mapping (rg :replica-group) :bool
     (if (endp rg)
         t
         (and (== (caar rg) (mget :addr (cdar rg)))
          (valid-replica-mapping (cdr rg)))))

(definec valid-replicas-data (replicas :lorep data :replica-data) :bool
     (if (lendp replicas)
         t
         (and (is-prefix (mget :data (first replicas)) data)
          (valid-replicas-data (rest replicas) data))))

(definec valid-replica-buffer (buffer :replica-buffer data :replica-data base :replica-data) :bool
     (if (endp buffer)
         t
         (let ((idx (caar buffer))
           (val (cdar buffer)))
           (and (< (llen data) idx)     ;; value can't yet be applied
            (< idx (llen base))     ;; corresponding value in primary's data
            (== (nth idx base) val) ;; values match
            (valid-replica-buffer (cdr buffer) data base)))))

(definec valid-replicas-buffer (replicas :lorep base :replica-data) :bool
     (if (lendp replicas)
         t
         (and (valid-replica-buffer (mget :buffer (car replicas)) (mget :data (car replicas)) base)
          (valid-replicas-buffer (rest replicas) base))))

;; Returns t if replica-group state is valid. Nil otherwise.
(definec valid-replica-group (rg :replica-group) :bool
     (and
      ;; rg contains at least one replica
      (! (endp rg))
      ;; All replicas are valid
      (valid-replicas rg)
      ;; rg contains exactly one primary
      (= 1 (num-primaries rg))
      ;; rg key equal corresponding replica's :addr
      (valid-replica-mapping rg)

      (let ((primary (get-primary rg))
        (backups (get-backups rg)))
        ;; Primary's :backups contains all backup replica addresses
        (let ((paddr (mget :addr primary))
          (baddrs (mget :backups primary)))
          (== (map-keys (mset paddr nil rg)) ;; FIX: they must be permutations of one another
          (map-keys baddrs)))
        ;; Each backup's :data is prefix of primary's :data
        (valid-data-prefix (mget :data primary) backups)
        ;; Each backup's :buffer contains entries not in backup's :data
        ;; and which correspond to primary's :data.
        (valid-buffer (mget :data primary) backups))))

#|

Network defdatas

|#

;(defdata value-type int)

(defdata read-req  (list 'READ-REQ))
(defdata read-res  (list 'READ-RESP value-type))
(defdata write-req (list 'WRITE-REQ value-type))
(defdata write-res (list 'WRITE-RESP))
(defdata repl-req  (list 'REPL-REQ nat value-type))
(defdata repl-res  (list 'REPL-RESP))

(defdata operation (oneof read-req read-res write-req write-res repl-req repl-res))

(operationp (list 'READ-REQ))
(operationp (list 'READ-RESP 1))
(operationp (list 'WRITE-REQ 1))
(operationp (list 'WRITE-RESP))
(operationp (list 'REPL-REQ 1 2))
(operationp (list 'REPL-RESP))

(defdata packet (record
                 (src . address)
                 (dst . address)
                 (op  . operation)))
(defdata network (listof packet))


#|

Network validity predicates

|#


#|

Replica transition functions

|#

(set-ignore-ok t)

(defdata trans-return-type (list replica network))

(definec trans-replica-read-req (r :replica dst :address) :trans-return-type ;;TODO
         (let* ((history (mget :data r))
                (val (if (endp history) 0 (car (last history))))
                (self-address (mget :addr r))
                (response `(READ-RESP , val))
                (response-packet (packet self-address dst response)))
           (list r (list response-packet))))

(definec generate-packets-list (target-list :loaddr src :address op :operation) :network
         (if (endp target-list)
             ()
             (append
              (list (packet src
                            (car target-list)
                            op))
              (generate-packets-list (cdr target-list) src op))))

(definec generate-packets (target-map :soaddr src :address op :operation) :network
         (generate-packets-list (map-keys target-map) src op))

(definec append-packet (p :packet n :network) :network
         (append (list p) n))

(definec update-history (r :replica history :replica-data) :replica
         (mset :data history r))

(definec update-buffer (r :replica buffer :replica-buffer) :replica
         (mset :buffer buffer r))

(definec trans-replica-write-req (r :replica dst :address write-value :value-type) :trans-return-type ;;TODO
         (let* ((history      (mget :data r))
                (self-address (mget :addr r))

                (new-history (append history write-value))
                (new-replica (update-history r new-history))

                (write-response (list 'WRITE-RESP))
                (write-response-packet (packet self-address dst write-response))
                (replication-request `(REPL-REQ , (len new-history) , write-value))
                (replication-request-packets (generate-packets (mget :backups r)
                                                                self-address
                                                                replication-request)))
           (if (primaryp r)
               (list new-replica (append-packet write-response-packet replication-request-packets))
               (list r          '()))))

(defdata pair-data-buffer (cons replica-data replica-buffer))
(defdata listof-keys (listof nat))
(definec select-keys-impl (keys :listof-keys buffer :replica-buffer output :replica-buffer) :replica-buffer
         (let* ((key (car keys))
                (value (mget key buffer)))
           (if (endp keys)
               output
               (if (== value nil)
                   (select-keys-impl (cdr keys) buffer output)
                   (select-keys-impl (cdr keys) buffer (mset key value output))))))

(definec select-keys (keys :listof-keys buffer :replica-buffer) :replica-buffer
         (select-keys-impl keys buffer '()))

(include-book "sorting/msort" :dir :system)

(definec update-data (current-history :replica-data buffer :replica-buffer) :pair-data-buffer
         (let* ((maxindex          (len current-history))
                (key-index         (map-keys buffer))
                (sorted-key-index  (acl2::msort key-index))

                (first-key         (car sorted-key-index))
                (first-value       (mget first-key buffer))
                (new-history       (append current-history first-value))

                (rest-keys         (cdr sorted-key-index)))
           (if (== maxindex first-key)
               (update-data current-history (select-keys rest-keys buffer))
               (cons current-history buffer))))

; (keys-should-apply (loop$ for x in sorted-key-index when (<= maxindex x) collect x))
; replica-buffer: map[nat] = nat

(definec trans-replica-repl-req (r :replica dst :address index :nat value :value-type) :trans-return-type
         (let* ((history      (mget :data   r))
                (self-address (mget :addr   r))
                (buffer       (mget :buffer r))

                (new-stat-pair (update-data history buffer))
                (new-history  (car new-stat-pair))
                (new-buffer   (cdr new-stat-pair))

                (replication-response `(REPL-RESP))
                (replication-response-packet (packet self-address dst replication-response))

                (new-replica (update-buffer (update-history r new-history) new-buffer)))
           (list new-replica (list replication-response-packet))))

(definec transition-replica (r :replica op :operation dst :address) :trans-return-type ;;TODO
     (match op
         (:read-req  (trans-replica-read-req  r dst))
         (:write-req (trans-replica-write-req r dst (second op)))
         (:repl-req  (trans-replica-repl-req  r dst (second op) (third op)))
         (& (list r '()))))

(definec transition-replica-group (rg :replica-group p :packet) :trans-return-type ;; TODO
         (let* ((src (mget :src p))
                (dst (mget :dst p))
                (op  (mget :op  p))
                (r   (mget dst  rg)))
           (if r
               (transition-replica r op src)
               (list rg '()))))
