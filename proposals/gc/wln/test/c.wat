  (module
    (func $0 (import "a" "g"))
    (func $1 (import "d/b" "h"))
    (func $2 (import "e" "f"))
    (func $3 (export "k") (call 0) (call 1) (call 2))
    (start 2)
  )
