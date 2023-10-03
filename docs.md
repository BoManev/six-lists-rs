# Stacked Borrows

## Compiles
```rust 
// data <- top
let mut data = 10;
// data - ref1 <- top
let ref1 = &mut data;
// data - ref1 - ref2 <- top
let ref2 = &mut *ref1;

// pop [ref2..]
// data - ref1 - ref2 <- top
*ref2 += 2;
// pop [ref1..]
// data - ref1 <- top
*ref1 += 1;
// no access to ref2 and we good
```

## Errors
``` rust
// data <- top
let mut data = 10;
// data - ref1 <- top
let ref1 = &mut data;
// data - ref1 - ref2 <- top
let ref2 = &mut *ref1;

// pop [ref1..]
// data - ref1 <- top
*ref1 += 2;
// ref2 must be on the top of the stack for all uses
*ref2 += 1;
```

### Misc
Don't mix reference with raw pointers; keep the stacked borrows heuristic

Experimental strict-mode
```bash
MIRIFLAGS="-Zmiri-tag-raw-pointers" cargo +nightly miri test
```