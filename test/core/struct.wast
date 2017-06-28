;; Test syntax of struct types.

(module
  (type (struct))
  (type (struct (field i32)))
  (type (struct (field i32) (field i32)))
  (type (struct (field $x i32) (field $y i32)))
  (type (struct (field i32 i32)))
  (type (struct (field) (field i32 i32) (field $a i32) (field i64 i32)))
)


;; Test binding structure of struct types.

(module
  (type $s0 (struct (field (ref 0) (ref 1) (ref $s0) (ref $s1))))
  (type $s1 (struct (field (ref 0) (ref 1) (ref $s0) (ref $s1))))

  (func (param (ref $forward)))

  (type $forward (struct))
)

(assert_invalid
  (module (type (struct (field (ref 1)))))
  "unknown type"
)

(assert_invalid
  (module (type (struct (field (ref 1)))) (type (func)))
  "reference to non-structure type"
)

(assert_invalid
  (module (func (param (ref 1))))
  "unknown type"
)

(assert_invalid
  (module (func (param (ref 0))))
  "reference to non-structure type"
)


;; Test execution of basic struct insructions.

(module
  (type $vec (struct (field f32) (field $y f32) (field $z f32)))

  (func $get_0 (param $v (ref $vec)) (result f32)
    (get_field $vec 0 (get_local $v))
  )
  (func (export "get_0") (result f32)
    (call $get_0 (new $vec))
  )

  (func $set_get_y (param $v (ref $vec)) (param $y f32) (result f32)
    (set_field $vec $y (get_local $v) (get_local $y))
    (get_field $vec $y (get_local $v))
  )
  (func (export "set_get_y") (param $y f32) (result f32)
    (call $set_get_y (new $vec) (get_local $y))
  )

  (func $set_get_1 (param $v (ref $vec)) (param $y f32) (result f32)
    (set_field $vec 1 (get_local $v) (get_local $y))
    (get_field $vec $y (get_local $v))
  )
  (func (export "set_get_1") (param $y f32) (result f32)
    (call $set_get_1 (new $vec) (get_local $y))
  )
)

(assert_return (invoke "get_0") (f32.const 0))
(assert_return (invoke "set_get_y" (f32.const 7)) (f32.const 7))
(assert_return (invoke "set_get_1" (f32.const 7)) (f32.const 7))


;; Test static and dynamic equivalence of simple struct types.

(module
  (type $vec1 (struct (field f32 f32 f32)))
  (type $vec2 (struct (field $x f32) (field $y f32) (field $z f32)))
  (type $func (func (param (ref $vec1)) (result f32)))

  (table anyfunc (elem $callee))

  (func $callee (param $v (ref $vec2)) (result f32)
    (get_field $vec2 $x (get_local $v))
  )
  (func (export "call_indirect") (result f32)
    (call_indirect $func (new $vec2) (i32.const 0))
  )
)

(assert_return (invoke "call_indirect") (f32.const 0))


;; Test static and dynamic equivalence of indirect struct types.

(module
  (type $s0 (struct (field i32 f32)))
  (type $s1 (struct (field (ref $s0))))
  (type $s2 (struct (field (ref $s0))))
  (type $s3 (struct (field i32 (ref $s1))))
  (type $s4 (struct (field i32 (ref $s2))))
  (type $func (func (param (ref $s4)) (result i32)))

  (table anyfunc (elem $callee))

  (func $callee (param $v (ref $s3)) (result i32)
    (get_field $s3 0 (get_local $v))
  )
  (func (export "call_indirect") (result i32)
    (call_indirect $func (new $s3) (i32.const 0))
  )
)

(assert_return (invoke "call_indirect") (i32.const 0))


;; Test static and dynamic equivalence of recursive struct types.

(module
  (type $list1 (struct (field i32 (ref $list1))))
  (type $list2 (struct (field i32 (ref $list2))))
  (type $func (func (param (ref $list1)) (result i32)))

  (table anyfunc (elem $callee))

  (func $callee (param $v (ref $list2)) (result i32)
    (get_field $list2 0 (get_local $v))
  )
  (func (export "call_indirect") (result i32)
    (call_indirect $func (new $list2) (i32.const 0))
  )
)

(assert_return (invoke "call_indirect") (i32.const 0))


;; Test static and dynamic equivalence of isomorphic recursive struct types.

(module
  (type $list1 (struct (field i32 (ref $list1))))
  (type $list2 (struct (field i32 (ref $list3))))
  (type $list3 (struct (field i32 (ref $list2))))
  (type $func (func (param (ref $list1)) (result i32)))

  (table anyfunc (elem $callee))

  (func $callee (param $v (ref $list2)) (result i32)
    (get_field $list2 0 (get_local $v))
  )
  (func (export "call_indirect") (result i32)
    (call_indirect $func (new $list2) (i32.const 0))
  )
)

(assert_return (invoke "call_indirect") (i32.const 0))


(module
  (type $list1 (struct (field i32 (ref $list3))))
  (type $list2 (struct (field i32 (ref $list2))))
  (type $list3 (struct (field i32 (ref $list1))))
  (type $func (func (param (ref $list1)) (result i32)))

  (table anyfunc (elem $callee))

  (func $callee (param $v (ref $list2)) (result i32)
    (get_field $list2 0 (get_local $v))
  )
  (func (export "call_indirect") (result i32)
    (call_indirect $func (new $list2) (i32.const 0))
  )
)

(assert_return (invoke "call_indirect") (i32.const 0))


(module
  (type $t1 (struct (field i32 (ref $u1))))
  (type $u1 (struct (field f32 (ref $t1))))
  (type $t2 (struct (field i32 (ref $u3))))
  (type $u2 (struct (field f32 (ref $t3))))
  (type $t3 (struct (field i32 (ref $u2))))
  (type $u3 (struct (field f32 (ref $t2))))
  (type $func (func (param (ref $t1)) (result i32)))

  (table anyfunc (elem $callee))

  (func $callee (param $v (ref $t2)) (result i32)
    (get_field $t2 0 (get_local $v))
  )
  (func (export "call_indirect") (result i32)
    (call_indirect $func (new $t2) (i32.const 0))
  )
)

(assert_return (invoke "call_indirect") (i32.const 0))


;; Test link-time type equivalence

(module
  (type $vec (struct (field f32 f32 f32)))
  (func (export "f") (param (ref $vec)))
)
(register "M1")
(module
  (func (import "M1" "f") (param (ref $vec)))
  (type $vec (struct (field f32 f32 f32)))
)

(module
  (type $list (struct (field i32 (ref $list))))
  (func (export "f") (param (ref $list)))
)
(register "M2")
(module
  (type $list1 (struct (field i32 (ref $list2))))
  (type $list2 (struct (field i32 (ref $list1))))
  (func (import "M2" "f") (param (ref $list2)))
)

(module
  (type $list1 (struct (field i32 (ref $list2))))
  (type $list2 (struct (field i32 (ref $list1))))
  (func (export "f") (param (ref $list2)))
)
(register "M3")
(module
  (type $list (struct (field i32 (ref $list))))
  (func (import "M3" "f") (param (ref $list)))
)
