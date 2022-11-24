(in-package "ACL2S")

#|

Utility functions

|#

(definec uniquesp (l :tl) :bool
  (cond
    ((lendp l) t)
    ((in (first l) (rest l)) nil)
    (t (uniquesp (rest l)))))

(definec is-prefix (test :tl base :tl) :bool
	 (match (list test base)
	     (('() &) t)
	   (((& . &) '()) nil)
	   (((f1 . r1) (f2 . r2))
	    (if (== f1 f2)
		(is-prefix r1 r2)
		nil))))


#|

Replica defdatas

|#

(defdata value-type int)
(defdata addr-comp (range integer (0 <= _ < 256)))
(defdata address (list addr-comp addr-comp addr-comp addr-comp))
(defdata loaddr (listof address))

(defdata replica-role (enum '(PRIMARY BACKUP)))
(defdata replica-data (listof value-type))
(defdata replica-buffer (map nat value-type))
(defdata replica (record
		  (addr . address)
		  (role . replica-role)
		  (data . replica-data) ;; store committed data
		  (buffer . replica-buffer) ;; store out-of-order updates
		  (backups . loaddr)))

(defdata replica-group (map address replica))


#|

Replica initialization functions

|#

;; Initialize replica.
(definec init-replica (addr :address role :replica-role backups :loaddr) :replica
	 (replica addr role '() '() backups))

(definec init-replica-group-helper (addrs :loaddr backups :loaddr) :replica-group
	 :input-contract (and (! (lendp addrs))
			      (uniquesp addrs))
;;			      (is-prefix backups addrs)
	 (if (lendp (rest addrs))
             (mset (first addrs) (init-replica (first addrs) 'PRIMARY backups) '())
             (mset (first addrs) (init-replica (first addrs) 'BACKUP '())
                   (init-replica-group-helper (rest addrs) backups))))

;; Initialize replica group. The last address is assigned role of primary.
(definec init-replica-group (addrs :loaddr) :replica-group
	 :input-contract (and (! (lendp addrs))
			      (uniquesp addrs))
	 (init-replica-group-helper addrs (reverse (rest (reverse addrs)))))

#|

Replica utility functions

|#
(definec primaryp (r :replica) :bool
  (== 'PRIMARY (mget :role r)))


#|

Replica validity predicate

|#

;; Returns t if replica state is valid. Nil otherwise.
;; This should perform the following checks:
;; - replica's `buffer` keys are all > (len data)
(definec valid-replica (r :replica) :bool
	 ...)


;; Returns t if replica-group state is valid. Nil otherwise.
;; This should perform the following checks:
;; - rg contains at least one replica
;; - rg contains exactly one primary
;; - primary's member `backups` contains all backup replica addresses
;; - rg is a map of address to replica, so map key equals replica's member `addr`
;;   - this implies uniqueness of addresses
;; - all replicas' `data` is a prefix of primary's `data`
(definec valid-replica-group (rg :replica-group) :bool
	 ...)


#|

Network defdatas

|#

(defdata read-req   (list 'READ-REQ))
(defdata read-resp  (list 'READ-RESP value-type))
(defdata write-req  (list 'WRITE-REQ value-type))
(defdata write-resp (list 'WRITE-RESP))
(defdata repl-req   (list 'REPL-REQ nat value-type))
(defdata repl-resp  (list 'REPL-RESP))

(defdata operation (oneof read-req read-resp write-req write-resp repl-req repl-resp))
(defdata packet (record
                 (src . address)
                 (dst . address)
                 (op . operation)))
(defdata network (listof packet))


#|

Network validity predicates

|#


#|

Replica transition functions

|#

(definec trans-replica-read-req (r :replica dst :address) :any ;;TODO
	 (let* ((val (car (mget :data r)))
		(op `(READ-RESP ,val)))
	   (list r (list op))))

(definec transition-replica (r :replica op :operation dst :address) :any ;;TODO
	 (match op
	     (:read-req (trans-replica-read-req r dst))
	   (:write-req (trans-replica-write-req r dst (second op)))
	   (:repl-req (trans-replica-repl-req r dst (second op) (third op)))
	   (& (list r '()))))

(definec transition-replica-group (rg :replica-group p :packet) :any ;; TODO
	 (let* ((src (mget :src p))
		(dst (mget :dst p))
		(op (mget :op p))
		(r (mget dst rg)))
	   (if r
	       (transition-replica r op src)
	       (list rg '()))))
