;; TODO: more tests

;; Validation

(module
  (rec
    (type $t1 (struct (field i32 (ref $t1))))
  )
  (rec
    (type $t2 (sub $t1 (struct (field i32 (ref $t3)))))
    (type $t3 (sub $t1 (struct (field i32 (ref $t2)))))
  )
)

(module
  (rec
    (type $t1 (func (param i32 (ref $t3))))
    (type $t2 (sub $t1 (func (param i32 (ref $t2)))))
    (type $t3 (sub $t2 (func (param i32 (ref $t1)))))
  )

  (func $f1 (param $r (ref $t1))
    (call $f1 (local.get $r))
  )
  (func $f2 (param $r (ref $t2))
    (call $f1 (local.get $r))
    (call $f2 (local.get $r))
  )
  (func $f3 (param $r (ref $t3))
    (call $f1 (local.get $r))
    (call $f2 (local.get $r))
    (call $f3 (local.get $r))
  )
)

(module
  (rec
    (type $t1 (func (result i32 (ref $u1))))
    (type $u1 (func (result f32 (ref $t1))))
  )

  (rec
    (type $t2 (sub $t1 (func (result i32 (ref $u3)))))
    (type $u2 (sub $u1 (func (result f32 (ref $t3)))))
    (type $t3 (sub $t1 (func (result i32 (ref $u2)))))
    (type $u3 (sub $u1 (func (result f32 (ref $t2)))))
  )

  (func $f1 (param $r (ref $t1))
    (call $f1 (local.get $r))
  )
  (func $f2 (param $r (ref $t2))
    (call $f1 (local.get $r))
    (call $f2 (local.get $r))
  )
  (func $f3 (param $r (ref $t3))
    (call $f1 (local.get $r))
    (call $f3 (local.get $r))
  )
)


;; Recursive types.

(module
  (rec (type $t1 (func (result (ref null $t1)))))
  (rec (type $t2 (sub $t1 (func (result (ref null $t2))))))

  (func $f1 (type $t1) (ref.null $t1))
  (func $f2 (type $t2) (ref.null $t2))
  (table funcref (elem $f1 $f2))

  (func (export "run")
    (block (result (ref null $t1)) (call_indirect (type $t1) (i32.const 0)))
    (block (result (ref null $t1)) (call_indirect (type $t1) (i32.const 0)))
    (block (result (ref null $t1)) (call_indirect (type $t1) (i32.const 1)))
    (block (result (ref null $t1)) (call_indirect (type $t1) (i32.const 1)))
    (block (result (ref null $t2)) (call_indirect (type $t2) (i32.const 1)))
    (block (result (ref null $t2)) (call_indirect (type $t2) (i32.const 1)))
    (br 0)
  )
)
(assert_return (invoke "run"))
