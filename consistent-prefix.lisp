(in-package "ACL2S")

#|

Utility functions

|#

(definec is-prefix-of (test :tl base :tl) :bool
	 (cond
	   ((lendp test) t)
	   ((lendp base) nil)
	   ((== (first test) (first base))
	    (is-prefix-of (rest test) (rest base)))
	   (t nil)))

(definec is-suffix-of (test :tl base :tl) :bool
	 (is-prefix-of (reverse test) (reverse base)))

(definec alowfkeyp (l :alist) :bool
	 (if (lendp l)
	     t
	     (and (wf-keyp (caar l))
		  (alowfkeyp (rest l)))))

(definec alist-2-map (l :alist) :all
	 :input-contract (alowfkeyp l)
	 :output-contract (good-map (alist-2-map l))
	 (if (lendp l)
	     '()
	     (mset (caar l) (cdar l) (alist-2-map (cdr l)))))

#|

Custom Set Implementation

|#

;; To declare a set type, use map and have the value type be 'none.

(defdata none 'none)
(defmacro sadd (v s) (list 'mset v ''none s))
(defmacro srem (v s) (list 'mset v 'nil s))
(defmacro smem (v s) (list 'mget v s))

(definec s2l (s :all) :tl
	 :input-contract (good-map s)
	 (if s
	     (cons (caar s) (s2l (cdr s)))
	     '()))

(definec lowfkeyp (l :tl) :bool
	 (if (lendp l)
	     t
	     (and (wf-keyp (first l))
		  (lowfkeyp (rest l)))))

(definec l2s (l :tl) :all
	 :input-contract (lowfkeyp l)
	 :output-contract (good-map (l2s l))
	 (if (lendp l)
	     '()
	     (sadd (first l) (l2s (rest l)))))


;; NOTE: Map type doesn't work in current version of ALC2s.
;; Therefore, it was suggested to use alistof instead.
(defdata key-type int) ;; TODO: getting errors with symbol and string
(defdata val-type (oneof int 'nil))

(defdata addr-comp (range integer (0 <= _ < 256)))
(defdata address (list addr-comp addr-comp addr-comp addr-comp))
(defdata loaddr (listof address))
(defdata soaddr (map address none))
(property address-s2l-type-remains (x :all)
  :hyps (soaddrp x)
  :body (loaddrp (s2l x)))
(in-theory (disable addressp))


#|

Replica defdatas

|#

;; All writes are ordered at the primary and the backups apply the
;; updates in the order specified by the primary. This means that
;; each write should have an associated index number and are applied
;; according to their index.
(defdata replica-role          (enum '(PRIMARY BACKUP)))
(defdata replica-memory        (map key-type val-type))       ; current kv mapping
(property mget-replica-memory-rettype (mem key)
  :hyps (and (replica-memoryp mem) (wf-keyp key))
  :body (val-typep (mget key mem)))
(defdata kv-pair (cons key-type val-type))
(defdata replica-buffer        (map nat kv-pair))             ; out-of-order writes
(defdata replica-write-history (alistof key-type val-type)) ; history of applied writes

(defdata replica (record
                  (addr    . address)
                  (role    . replica-role)
                  (backups . soaddr)
                  (memory  . replica-memory)
                  (buffer  . replica-buffer)
		  (nxt-idx . nat)
                  (history . replica-write-history)))

(defdata replica-group (map address replica))
(defdata lorep (listof replica))


#|

Replica creation functions

|#

;; Initialize replica group.
(definec init-replica (addr :address role :replica-role backups :soaddr) :replica
	 :function-contract-hints (("goal" :use ((:instance replica-constructor-pred
							    (replica-addr addr)
							    (replica-role role)
							    (replica-backups backups)
							    (replica-memory '())
							    (replica-buffer '())
							    (replica-nxt-idx 0)
							    (replica-history '())))))
         (replica addr role backups '() '() 0 '()))

(definec init-replica-group-helper (addrs :loaddr primary :address backups :soaddr) :replica-group
	 :function-contract-hints (("goal" :in-theory (disable addressp init-replica-definition-rule)))
	 ;;input-contract (and
	 ;; (! (mget primary backups))
	 ;; (contains-keys addrs backups))
	 (if (lendp addrs)
             (mset primary (init-replica primary 'PRIMARY backups) '())
             (mset (first addrs) (init-replica (first addrs) 'BACKUP '())
                   (init-replica-group-helper (rest addrs) primary backups))))

(definec init-replica-group (primary :address backups :soaddr) :replica-group
	 ;;     :input-contract (! (mget primary backups))
	 (init-replica-group-helper (s2l backups) primary backups))


#|

Replica utility functions

|#

(definec primaryp (r :replica) :bool
	 (== 'PRIMARY (mget :role r)))

(definec num-primaries (rg :replica-group) :nat
	 (if (endp rg)
             0
             (+ (if (primaryp (cdar rg)) 1 0)
		(num-primaries (cdr rg)))))

(definec single-primaryp (rg :replica-group) :bool
	 (= 1 (num-primaries rg)))

(definec get-primary (rg :replica-group) :replica
	 :input-contract (single-primaryp rg)
	 (if (primaryp (cdar rg))
             (cdar rg)
             (get-primary (rest rg))))

(definec get-backups (rg :replica-group) :lorep
	 (if (endp rg)
             '()
             (if (! (primaryp (cdar rg)))
		 (cons (cdar rg) (get-backups (rest rg)))
		 (get-backups (rest rg)))))


#|

Packet defdatas

|#

(defdata op-type (enum '(READ-REQ READ-RES WRITE-REQ WRITE-RES REPL-REQ REPL-RES)))
(defdata operation (oneof
		    (list op-type key-type val-type nat)
		    (list op-type key-type val-type)
		    (list op-type key-type)
		    (list op-type)))

(definec read-reqp (v :all) :bool
	 (and (operationp v)
	      (= (llen v) 2)
	      (== (car v) 'READ-REQ)))
(definec read-resp (v :all) :bool
	 (and (operationp v)
	      (= (llen v) 3)
	      (== (car v) 'READ-RES)))
(definec write-reqp (v :all) :bool
         (and (operationp v)
	      (= (llen v) 3)
	      (== (car v) 'WRITE-REQ)))
(definec write-resp (v :all) :bool
	 (and (operationp v)
	      (= (llen v) 1)
	      (== (car v) 'WRITE-RES)))
(definec repl-reqp (v :all) :bool
         (and (operationp v)
	      (= (llen v) 4)
	      (== (car v) 'REPL-REQ)))
(definec repl-resp (v :all) :bool
	 (and (operationp v)
	      (= (llen v) 1)
	      (== (car v) 'REPL-RES)))

(definec init-read-req (k :key-type) :operation
	 :output-contract (read-reqp (init-read-req k))
	 (list 'READ-REQ k))
(definec init-read-res (k :key-type v :val-type) :operation
	 :output-contract (read-resp (init-read-res k v))
	 (list 'READ-RES k v))
(definec init-write-req (k :key-type v :val-type) :operation
	 :output-contract (write-reqp (init-write-req k v))
	 (list 'WRITE-REQ k v))
(definec init-write-res () :operation
	 :output-contract (write-resp (init-write-res))
	 (list 'WRITE-RES))
(definec init-repl-req (k :key-type v :val-type i :nat) :operation
	 :output-contract (repl-reqp (init-repl-req k v i))
	 (list 'REPL-REQ k v i))
(definec init-repl-res () :operation
         :output-contract (repl-resp (init-repl-res))
         (list 'REPL-RES))

(defdata packet (record
                 (src . address)
                 (dst . address)
                 (op  . operation)))
(defdata network (listof packet))


#|

Packet creation functions

|#

(definec init-packet (src :address dst :address op :operation) :packet
	 :function-contract-hints (("goal" :use (:instance packet-constructor-pred
							   (packet-src src)
							   (packet-dst dst)
							   (packet-op op))))
	 (packet src dst op))


#|

Replica transition defdatas

|#

(defdata r-trans-return-type (cons replica network))
(defdata rg-trans-return-type (cons replica-group network))


#|

Replica transition functions

|#

(definec trans-replica-read-req (r :replica dst :address key :key-type) :r-trans-return-type
	 :function-contract-hints (("Goal'" :in-theory (disable init-packet-definition-rule)))
         (let* ((val (mget key (mget :memory r)))
                (op (init-read-res key val))
		(src (mget :addr r))
		(resp (init-packet src dst op)))
	   (cons r (list resp))))

(definec generate-broadcast-packets (src :address dsts :loaddr op :operation) :network
	 :function-contract-hints (("Goal" :in-theory (disable init-packet-definition-rule)))
         (if (lendp dsts)
             '()
             (cons (init-packet src (first dsts) op)
		   (generate-broadcast-packets src (rest dsts) op))))

;; TODO: Proved up to THIS point
(definec replica-apply-write (r :replica idx :nat key :key-type val :val-type) :replica
	 (let ((nxt-idx (mget :nxt-idx r)))
	   (cond
	     ((= nxt-idx idx)
	      (let* ((mem (mget :memory r))
		     (nxt-idx (mget :nxt-idx r))
		     (hist (mget :history r))
		     (new-mem (mset key val mem))
		     (new-nxt-idx (1+ nxt-idx))
		     (new-hist (acons key val hist))
		     (new-r (mset :history new-hist
				  (mset :nxt-idx new-nxt-idx
					(mset :memory new-mem r)))))
		(b* ((buf (mget :buffer new-r))
		     (maybe-wr (mget new-nxt-idx buf))
		     ((when (! maybe-wr)) new-r)
		     (new-buf (mset new-nxt-idx nil buf))
		     (new-new-r (mset :buffer new-buf new-r))
		     (nxt-key (car maybe-wr))
		     (nxt-val (cdr maybe-wr)))
		  (replica-apply-write new-new-r new-nxt-idx nxt-key nxt-val))))
	     ((< nxt-idx idx)
	      (let* ((buf (mget :buffer r))
		     (new-buf (mset idx (cons key val) buf))
		     (new-r (mset :buffer new-buf r)))
		new-r))
	   ;; The only way for (> nxt-idx idx) to be true is for
	   ;; duplicate packet to be sent. This should never happen.
	   (t r))))

(definec trans-replica-write-req (r :replica dst :address key :key-type val :val-type) :r-trans-return-type
         (b* (((when (! (primaryp r))) (cons r '()))
	      (nxt-idx (mget :nxt-idx r))
	      (new-r (replica-apply-write r nxt-idx key val))
	      
              (self-address (mget :addr r))
              (write-response (init-write-res))
              (write-response-packet (init-packet self-address dst write-response))
              (replication-request (init-repl-req key val nxt-idx))
	      (backups (s2l (mget :backups r)))
              (replication-request-packets (generate-broadcast-packets self-address backups replication-request)))
           (cons new-r (cons write-response-packet replication-request-packets))))

(definec trans-replica-repl-req (r :replica dst :address idx :nat key :key-type val :val-type) :r-trans-return-type
         (b* (((when (primaryp r)) (cons r '()))
	      (new-r (replica-apply-write r idx key val))
	      (src (mget :addr r))
              (op (init-repl-res))
	      (resp (init-packet src dst op)))
           (cons new-r (list resp))))

(definec transition-replica (r :replica op :operation src :address) :r-trans-return-type
	 (cond
           ((read-reqp op)
	    (trans-replica-read-req r src (nth 1 op)))
           ((write-reqp op)
	    (trans-replica-write-req r src (nth 1 op) (nth 2 op)))
           ((repl-reqp op)
	    (trans-replica-repl-req r src (nth 3 op) (nth 1 op) (nth 2 op)))
           (t (cons r '()))))

(definec transition-replica-group (rg :replica-group p :packet) :rg-trans-return-type
	 (b* ((src (mget :src p))
	      (dst (mget :dst p))
	      (op (mget :op p))
	      (r (mget dst rg))
              ((when (! r)) (cons rg '()))
              (trans (transition-replica r op src))
              (r2 (car trans))
              (pkts (cdr trans))
              (rg2 (mset dst r2 rg)))
	   (cons rg2 pkts)))

#|

System state defdatas

|#

(defdata system-state (cons replica-group network))

(definec init-system-state (primary :address backups :soaddr) :system-state
	 (cons (init-replica-group primary backups) '()))

#|

System state transition defdatas

|#

(defdata event (oneof nat packet))
(defdata events (listof event))


#|

System state transition functions

|#

(definec transition-system-state (st :system-state ev :event) :system-state
	 (let ((rg (car st))
               (net (cdr st)))
	   (match ev
             (:packet (cons rg (cons ev net)))
             (:nat
              (b* ((pkt (nth ev net))
		   ((when (! pkt)) st)
		   (net-wo-pkt (append (take ev net) (nthcdr (1+ ev) net)))
		   (trans (transition-replica-group rg pkt))
		   (rg2 (car trans))
		   (net2 (append (cdr trans) net-wo-pkt)))
		(cons rg2 net2))))))

(definec transition (st :system-state evs :events) :system-state
	 (if (lendp evs)
	     st
	     (let* ((ev (first evs))
		    (st2 (transition-system-state st ev)))
	       (transition st2 (rest evs)))))

(let* ((primary '(1 1 1 1))
       (backups (l2s '((2 2 2 2) (3 3 3 3))))
       (st (init-system-state primary backups))
       (evs `(
	      ,(init-packet '(0 0 0 0) '(1 1 1 1) (init-write-req 0 0))
	       ,(init-packet '(0 0 0 0) '(1 1 1 1) (init-write-req 1 1))
	       ,(init-packet '(0 0 0 0) '(1 1 1 1) (init-write-req 2 2))
	       2
	       0
	       2
	       0
	       0
	       3)
	 ))
  (transition st evs))


#|

Properties to prove

|#

;(definec histories-are-prefix (replicas :lorep history :replica-write-history) :bool
 ;    (if (lendp replicas)
  ;       t
;	 ;; use suffix since history grows from front
 ;        (and (is-suffix-of (mget :history (car replicas)))
  ;            (histories-are-prefix (cdr replicas) history))))
;
;(definec history-prefixp (state :system-state) :bool
 ;    (b* ((replicas (mget :replicas state))
  ;        ((when (! (whole-brainp replicas))) nil)
   ;       (primary (get-primary replicas))
    ;      (backups (get-backups replicas))
     ;     (primary-history (mget :history primary)))
      ; (histories-are-prefix backups primary-history)))

;(definec history-increasingp (prev-state next-state :system-state) :bool
 ;    (b* ((prev-reps (mget :replicas prev-state))
  ;        (next-reps (mget :replicas next-state))
   ;       )))

#|

Functions for proving desired properties

|#

(definec init-replica-groupp (rg :replica-group) :bool
	 (b* (((when (! (single-primaryp rg))) nil)
              (primary (get-primary rg))
              (paddr (mget :addr primary))
              (backaddrs (mget :backups primary)))
           (== rg (init-replica-group paddr backaddrs))))

(definec init-networkp (net :network) :bool
	 (lendp net))

(definec init-system-statep (st :system-state) :bool
	 (and (init-replica-groupp (car st))
	      (init-networkp (cdr st))))

(definec history-prefix-of (test :replica base :replica) :bool
	 ;; use suffix since history grows from front
	 (is-suffix-of (mget :history test) (mget :history base)))

(definec history-prefixp-helper (primary :replica backups :lorep) :bool
	 (if (lendp backups)
	     t
	     (and (history-prefix-of (first backups) primary)
		  (history-prefixp-helper primary (rest backups)))))

(definec history-prefixp (st :system-state) :bool
	 :input-contract (single-primaryp (car st))
	 (let* ((rg (car st))
		(primary (get-primary rg))
		(backups (get-backups rg)))
	   (history-prefixp-helper primary backups)))

(definec history-increasingp-helper (test-rg :replica-group base-rg :replica-group) :bool
	 (b* (((when (endp test-rg)) t)
	      (addr (caar test-rg))
	      (test-rep (cdar test-rg))
	      (base-rep (mget addr base-rg))
	      ((when (! base-rep)) nil))
	   (and (history-prefix-of test-rep base-rep)
		(history-increasingp-helper (cdr test-rg) base-rg))))

(definec history-increasingp (prev :system-state next :system-state) :bool
	 (let ((prev-rg (car prev))
	       (next-rg (car next)))
	   (history-increasingp-helper prev-rg next-rg)))

(definec memory-consistentp-helper (rg :replica-group) :bool
	 (b* (((when (endp rg)) t)
	      (r (cdar rg))
	      (mem (mget :memory r))
	      (hist (mget :history r))
	      (hmem (alist-2-map hist)))
	   (and (== mem hmem)
		(memory-consistentp-helper (cdr rg)))))


(definec memory-consistentp (st :system-state) :bool
	 (memory-consistentp-helper (car st)))

#|

Desired properties

|#

;; Each backup's history member is a prefix of that of the primary.
(property backups-prefix-of-primary (init :system-state st :system-state evs :events)
  :hyps (and (init-system-statep init)
	     (== st (transition init evs)))
  :body (history-prefixp st))

;; Each replica's history member is a prefix of itself after each step.
(property replica-histories-increasing (init :system-state st :system-state evs :events st-prime :system-state ev :event)
  :hyps (and (init-system-statep init)
	     (== st (transition init evs))
	     (== st-prime (transition-system-state st ev)))
  :body (history-increasingp st st-prime))

;; Each replica's memory is consistent with its memory.
(property replica-memory-consistency (init :system-state st :system-state evs :events)
  :hyps (and (init-system-statep init)
             (== st (transition init evs)))
  :body (memory-consistentp st))



;; TODO: define is-prefix-of, event packets can only be reads or writes!!
