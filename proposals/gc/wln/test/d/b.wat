  (module
    (func $0 (import "a" "f"))
    (func $1 (import "e" "a"))
    (func $2 (export "f") (call 0))
    (func $3 (export "h") (call 1) (call 2))
  )
