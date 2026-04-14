/* encoding of runtime error with global flag */
/* example lowErrow in Fig 3 of Hypra OOPSLA'24 */

// globals; whether a runtime error has occurred
var err, err': bool; 

// since can't pass by ref, use flag whether err or err'
procedure errAssert(b: bool);
   requires !err;
   ensures err <==> !b;
   modifies err; 

procedure errAssert'(b: bool);
   requires !err';
   ensures err' <==> !b;
   modifies err'; 

procedure lowError(hi, lo: int)
  requires !err;
  modifies err; 
{ 
  if (hi > 0) { 
    call errAssert( lo >= 0 ); 
  }
  if (!err) {      // continue if no err so far 
    if (lo < 0) { 
      call errAssert( false ); 
    }
  }
}

procedure lowError_NI(hi, lo, hi', lo': int) 
  requires !err && !err' ;
  requires lo == lo' ;
  ensures err <==> err' ;
  modifies err, err';
{ 
  // sequential alignment
  if (hi > 0) { call errAssert( lo >= 0 ); }
  if (!err) {
    if (lo < 0) { call errAssert( false ); }
  }
  if (hi' > 0) { call errAssert'( lo' >= 0 ); }
  if (!err') {
    if (lo' < 0) { call errAssert'( false ); }
  }
}

