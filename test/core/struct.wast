(module
  (type (struct))
  (type (struct))
  (type (struct (field i32)))
  (type (struct (field i32) (field i32)))
  (type (struct (field $x i32) (field $y i32)))
  (type (struct (field i32 i32)))
  (type (struct (field) (field i32 i32) (field $a i32) (field i64 i32)))
)

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

(module
  (type $vec1 (struct (field f32 f32 f32)))
  (type $vec2 (struct (field $x f32) (field $y f32) (field $z f32)))
  (type $func (func (param (ref $vec1)) (result f32)))

  (table anyfunc (elem $callee))

  (func $callee (param $v (ref $vec2)) (result f32)
    (get_field $vec2 $x (get_local $v))
  )
  (func (export "call_indirect") (result f32)
    (call_indirect $func (new $vec1) (i32.const 0))
  )
)

(assert_return (invoke "call_indirect") (f32.const 0))
