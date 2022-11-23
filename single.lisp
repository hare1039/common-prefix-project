(in-package "ACL2S")

(defdata data (record
               (key     . string)
               (value   . string)
               (version . nat)))

(definec new-data () :data
         (data "" "" 0))

;(definec data-version++ (d :data) :data
;         ())

(defdata operation-type (enum '(read read-response write write-response)))
(defdata operation (cons operation-type data))

(defdata peer-id nat)
(defdata peer-log (listof operation))
(defdata peer-list (listof peer-id))

(defdata event
    (record
     (dest . peer-id)
     (data . operation)
     (history . )
     ))

(defdata peer-state
    (record
     (id             . peer-id)
     (primary-id     . peer-id)
     (last-index     . nat)
     (commited-index . nat)
     (peers          . peer-list)
     (local-log      . peer-log)))

(definec new-peer-state () :peer-state
         (peer-state
          0
          0
          0
          0
          '()
          '()))

(definec peer-trans (p :peer-state e :event)


  )


(defdata group (listof (cons peer peer-state)))
