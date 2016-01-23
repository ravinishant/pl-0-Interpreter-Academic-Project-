// Baseline version of PL/0 in JS.
// Dec. 2014
// Pascal code obtained from www.moorecad.com/standardpascal
// pl/0 compiler with code generation from Wirth's Algorithms+Data Structures=Programs
// Event-driven from html, as in 3302 lab 1, fall 2014
// Corresponding state machine is states.jpg (from graphviz states.dot)
/*
3302 Lab 1, Spring 2013 BPW - add simple I/O
  1. "in"  stream may be used anywhere an r-value may be used.
  2. "out" stream may be used anywhere an l-value may be used.
  3. Input is taken to be one integer per line.
     -999999 terminates the input stream and is only passed on once.
     Second -999999 will abort.  "?" was the prompt.
  4. Output is one integer per line.
     Each output line starts with "!".
  5. The output stream does not terminate.
  6. Trace for "sto" has been disabled.
  7. The range check for error(30) has been corrected.
  8. "in" and "out" are identifiers for the two streams.  Like the
     rest of PL/0, these may be masked by other declarations.

May 2014, converted to JS, BPW
  1. Types are kept as comments.
  2. All-in-one compile and execute from html.
  3. Input starts on line after PL/0 code.
  4. Argument passing by value, like lab 4 spring 2013.
     http://ranger.uta.edu/~weems/NOTES3302/LAB4SPR13/plzero.args.pas
     Unlike Pascal solution, argument values are in the activation record
     rather than before it (with negative offsets).

May 20, 2014 separated into four windows with separate Run button
June 1, 2014 added rts window and step option (using closure), 
             along with forced recompile when PL/0 code is modified (see html).
June 6, 2014 added breakpoints, along with indication of frames in rts
June 22, 2014 extended for Lab 2, Summer 2014:  drawing and animation in canvas
June 27, 2014 extended for mouse movements
July 18, 2014 included arrays, Lab 3 Summer 2013
July 18, 2014 Lab 4 Summer 2014
              1. Mouse movements cvx, cvy with mousemove, mouseout
              2. C-style arrays declared in var as arr{length}
                 Interpreter does bounds checking for [0,length)
Dec 19, 2014 All names have flexible length, i.e. length limit of 10 is gone
             if .. then extended to  if .. then .. else
Dec 29, 2014 stop button causes RTS to be dumped
Jan 7, 2015 Cursor will be positioned over the token for the first compile error
            breaks added to block() for var and const syntax errors
Feb 6, 2015 Lab 1, Spring 2015
            \ Used as comment in scanner, rest of line is treated as a comment
            cvclick procedure to stop interpreter until mouseclick occurs
May 25, 2015 simplified canvas cursor position computation
May 26, 2015 promoted from pl0.lab1spr15.js to 3302 pl0.baseline.js
Aug 30, 2015 promoted from lab 2 summer 2015 to 3302 pl0.baseline.js
             Emojis, changed cursor for IDE state machine, asynchronous mouse click
Sep 6, 2015 moved state machine code out of interpreter and compiler driver
*/

var canvas, ctx, pic;

/* graphviz header
  node [shape=ellipse];
  blank [label="None\nEnabled"];
  compile [label="Compile\nEnabled"];
  run [label="Run\nEnabled"];
  runContinue [label="Run and Continue\nEnabled"];
  stop [label="Stop\nEnabled"];
*/

// constants to number enabled states
var blankState = 0,
  compileState = 1,
  runState = 2,
  runContinueState = 3,
  stopState = 4;
var envState = blankState, // The state of the user interface
  cvasclickFlag = false,   // indicates cvasclick handler is waiting for mouse click.
  cvasHandlerSave,         // Used when interpreter suspends.
  timeOutID; // Saved to allow cancelling interpreter continuing

function edit() { // keystroke detected in html sourcebox
  switch (envState) {
    case blankState: // blank -> compile [label="Editing"];
      envState = compileState;
      compileButton.disabled = false;
      break;
    case compileState: // compile -> compile [label="Editing"];
      break;
    case runState: // run -> compile [label="Editing"];
      runButton.disabled = true;
      envState = compileState;
      compileButton.disabled = false;
      listingbox.innerHTML =
        'Listing is now inconsistent with source\n' + listingbox.innerHTML;
      listingbox.scrollTop = 1;
      break;
    case runContinueState: // runContinue -> compile [label="Editing"];
      runButton.disabled = true;
      continueButton.disabled = true;
      envState = compileState;
      compileButton.disabled = false;
      listingbox.innerHTML =
        'Listing is now inconsistent with source\n' + listingbox.innerHTML;
      listingbox.scrollTop = 1;
      if (cvasclickFlag) {
        cvasclickFlag = false;
        canvas.onclick = undefined;
      }
      break;
    case stopState: // stop -> compile [label="Editing",style=dashed];
      stopButton.disabled = true;
      envState = compileState;
      compileButton.disabled = false;
      if (cvasclickFlag) { // Prevent incorrect awakening
        canvas.onclick = undefined;
        alert("(050) edit() has disabled canvas.onclick");
        cvasclickFlag = false;
        clearTimeout(timeOutID);
        alert("(70) edit() has killed timeOut " + timeOutID);
      }
      else if (canvas.onclick) { // Prevent incorrect awakening
        cvasHandlerSave = canvas.onclick;
        canvas.onclick = undefined;
        alert("(090) edit() has disabled canvas.onclick");
      }
      else { // a wait may cause the PL/0 machine to be triggered once more
        clearTimeout(timeOutID);
        alert("(100) edit() has killed timeOut " + timeOutID);
      }

      listingbox.innerHTML =
        'Listing is now inconsistent with source\n' + listingbox.innerHTML;
      listingbox.scrollTop = 1;
      break;
    default:
      alert("(200) edit: envState unknown: " + envState);
  }
  canvas.style.cursor = "not-allowed";
}

function run() {
	prepareCoveragegeList(); // html runButton clicked
	listcoverage(0);
  if (envState == runState) {
    // run -> stop [label="Run\nPressed"];
    runButton.disabled = true;
    envState = stopState;
    stopButton.disabled = false;
    initMachine();
    canvas.style.cursor = "pointer";
    interpret();
  }
  else if (envState == runContinueState) {
    // runContinue -> stop [label="Run or Continue\nPressed"];
    runButton.disabled = true;
    continueButton.disabled = true;
    envState = stopState;
    stopButton.disabled = false;
    cvasclickFlag = false; // in case previous execution was sitting suspended
    initMachine();
    canvas.style.cursor = "pointer";
    interpret();
  }
  else
    alert("(300) run: envState!=runState: " + envState);
}

var coveredCode = [];
var coveredCodeBackup = [];
function prepareCoveragegeList() {
	for(var i = 0; i< code.length; i++) {
		coveredCode[i] = code[i];
		if(coveredCodeBackup.length > 0)
			coveredCode[i].symbol = coveredCodeBackup[i].symbol;	
		else
			coveredCode[i].symbol = "   ";
	}
}

listcoverage = function(start) { /*list code generated for this block*/
    var i;
    var countStar = 0;
    var countPlus = 0;
    var countMinus = 0;
    var countBlank = 0;
    coveragebox.innerHTML = "";
    for (i = start; i < cx; i++) {
      coveragebox.innerHTML +=
       coveredCode[i].symbol + formatNumber(i, 5) + " " + mnemonic[coveredCode[i].f] + " " +
        formatNumber(coveredCode[i].l, 3) + " " + formatNumber(coveredCode[i].a, 5) + " "+
          (coveredCode[i].comment==undefined ? "" : coveredCode[i].comment)+
          "\n";
       if(coveredCode[i].symbol == "***") countStar+=1;
       if(coveredCode[i].symbol == "+++") countPlus+=1;
       if(coveredCode[i].symbol == "---") countMinus+=1;
       else if(coveredCode[i].symbol == "   ") countBlank+=1;
    }
    coveragebox.innerHTML+="\n *** " + countStar + "\n Uncovered " + countBlank;
    if(countPlus > 0)
    	coveragebox.innerHTML+="\n +++ " + countPlus;
    if(countMinus > 0)
    	coveragebox.innerHTML+="\n --- " + countMinus;
    coveredCodeBackup = coveredCode;
    coveragebox.scrollTop = 99999;
  };

function contin() { // html continueButton clicked
  if (envState == runContinueState) {
    // runContinue -> stop [label="Run or Continue\nPressed"];
    runButton.disabled = true;
    continueButton.disabled = true;
    envState = stopState;
    stopButton.disabled = false;
    if (cvasclickFlag) {
      canvas.onclick = cvasHandlerSave;
      alert("cvasclick before stop is being restored");
      canvas.style.cursor = "crosshair";
    }
    else
      canvas.style.cursor = "pointer";
    interpret();
  }
  else
    alert("(400) continue: envState!=runContinueState: " + envState);
}

function stop() { // html stopButton clicked
  if (envState == stopState) {
    // stop -> runContinue [label="Stop\nPressed",style=dashed];
    stopButton.disabled = true;
    envState = runContinueState;
    runButton.disabled = false;
    continueButton.disabled = false;
    if (cvasclickFlag) { // Prevent incorrect awakening
      cvasHandlerSave = canvas.onclick;
      canvas.onclick = undefined;
      alert("(450) stop() has disabled canvas.onclick");
      clearTimeout(timeOutID);
      alert("(470) stop() has killed timeOut " + timeOutID);
    }
    else if (canvas.onclick) { // Prevent incorrect awakening
      canvas.onclick = undefined;
      alert("(480) stop() has disabled canvas.onclick");
    }
    else { // a wait may cause the PL/0 machine to be triggered once more
      clearTimeout(timeOutID);
      alert("(500) stop() has killed timeOut " + timeOutID);
    }
    dumpRTSclosure();
    canvas.style.cursor = "not-allowed";
  }
  else
    alert("(600) stop: envState!=stopState: " + envState);
}

function terminateInterpreter() { // Normal or abnormal terminate
  // stop -> run [label="Clean\nTermination"];
  // stop -> run [label="Run-Time\nError"];
  // stop -> run [label="Call to\ndie"];
  stopButton.disabled = true;
  envState = runState;
  runButton.disabled = false;
  canvas.onclick = undefined; // prevent cvasclick
  cvasclickFlag = false;
  canvas.style.cursor = "not-allowed";
  dumpRTSclosure();
}

function suspendInterpreter() { // Allows restart or continuing    
  // stop -> runContinue [label="Call to\nstop"];
  stopButton.disabled = true;
  envState = runContinueState;
  runButton.disabled = false;
  continueButton.disabled = false;
  cvasHandlerSave = canvas.onclick;
  canvas.onclick = undefined;
  canvas.style.cursor = "not-allowed";
  dumpRTSclosure();
}

function compiledClean() {
  // compile -> run [label="Compiled\nClean"];
  envState = runState;
  runButton.disabled = false;
}

function compileError() {
  // compile -> blank [label="Compile\nError"];
  envState = blankState;
  listingbox.innerHTML += " errors in pl/0 program";
  listingbox.scrollTop = 99999;
} 

function getPosition(evt) {
  // new, simpler approach
  var rect = evt.currentTarget.getBoundingClientRect();

  return {x : (evt.clientX - rect.left) | 0, y : (evt.clientY - rect.top) | 0}; 
  }

function start_canvas() {
  // Starts page

  if (canvas.getContext)
    ctx = canvas.getContext('2d');
  else
    alert("start_canvas: no getContext");
}

// Load pictures for later use
pic = [];
pic[1] = new Image();
pic[2] = new Image();
pic[3] = new Image();
pic[1].src = "pic1.jpg";
pic[2].src = "pic2.jpg";
pic[3].src = "pic3.png";

cvxcvybox.innerHTML = "-999999 -999999";

// Assures canvas x and y positions are available before any pl/0 interpretation
// has occured.  Also see interpret() for replacement handlers.
canvas = document.getElementById('graphic');

canvas.style.cursor = "not-allowed";

canvas.onmousemove =
  function(evt) {
    var loc = getPosition(evt);
    cvxcvybox.innerHTML = loc.x + ' ' + loc.y;
  };
canvas.onmouseout =
  function() {
    cvxcvybox.innerHTML = "-999999 -999999";
  };

//constants
var norw = 12,
  /*no. of reserved words, including else*/
  kmax = 8,
  /*max. no. of digits in numbers, changed from nmax BPW*/
  // al = 10,          /*length of identifiers - eliminated fixed-length!!!*/
  nmax = 99999999,
  /*maximum value allowed in source program BPW*/
  levmax = 10; /*maximum depth of block nesting*/
/*type*/
/*symbol =
 (nul,ident,number,plus,minus,times,slash,oddsym,
  eql,neq,lss,leq,gtr,geq,lparen,rparen,comma,semicolon,
  period,becomes,beginsym,endsym,ifsym,thensym,
  whilesym,dosym,callsym,constsym,varsym,procsym,colon,lbrac,rbrac,elsesym);*/
// constants to replace symbol enumerated type from Pascal version
var nul = 0,
  ident = 1,
  number = 2,
  plus = 3,
  minus = 4,
  times = 5,
  slash = 6,
  oddsym = 7,
  eql = 8,
  neq = 9,
  lss = 10,
  leq = 11,
  gtr = 12,
  geq = 13,
  lparen = 14,
  rparen = 15,
  comma = 16,
  semicolon = 17,
  period = 18,
  becomes = 19,
  beginsym = 20,
  endsym = 21,
  ifsym = 22,
  thensym = 23,
  whilesym = 24,
  dosym = 25,
  callsym = 26,
  constsym = 27,
  varsym = 28,
  procsym = 29,
  colon = 30,
  lbrac = 31,
  rbrac = 32,
  elsesym = 33;

/*alfa = packed array [1..al] of char;*/
/*object1 = (constant,varible,proc,instream,outstream,vararr);*/
var constant = 0,
  varible = 1,
  proc = 2,
  instream = 3,
  outstream = 4,
  vararr = 5;
/* symset = set of symbol; use properties and proto inheritance to represent*/

/*fct = (lit,opr,lod,sto,cal,int,jmp,jpc,rdi,wro,lda,sta);*/
/*function codes, as called by Wirth.  AKA opcodes*/
var lit = 0,
  opr = 1,
  lod = 2,
  sto = 3,
  cal = 4,
  int = 5,
  jmp = 6,
  jpc = 7,
  rdi = 8,
  wro = 9,
  lda = 10,
  sta = 11;
/* instruction = packed record
                 f: fct;           function code
                 l: 0..levmax;     level
                 a: /*0..amax
                    integer        displacement address
              end; */
/*  lit 0,a  :  load constant a
    opr 0,a  :  execute operation a
    lod l,a  :  load varible l,a
    sto l,a  :  store varible l,a
    cal l,a  :  call procedure a at level l
    int 0,a  :  increment t-register by a
    jmp 0,a  :  jump to a
    jpc 0,a  :  jump conditional to a   
    rdi 0,0  : read from instream
    wro 0,0  : write to outstream
    lda l,a  : load from array (r-value)
    sta l,a  : store to array (l-value) */

var // These are maintained by the scanner
  ch, //: char;         /*last character read*/
  sym, //: symbol;       /*last symbol read*/
  id, //: alfa;         /*last identifier read*/
  num, //: integer;      /*last number read*/
  cc, //: integer;      /*character count*/
  ll, //: integer;      /*line length*/
  err, //: integer;

  // Jan 7, 2015 - these are for highlighting a problem token in sourcebox
  symbolStart, symbolEnd, getchPosition,

  // These are maintained by compiler
  cx, //: integer;      /*code allocation index*/
  line = [], //: array [1..81] of char;
  a = [], //: alfa;
  code = [], //: array [0..cxmax] of instruction;
  word = [], //: array [1..norw] of alfa;
  wsym = [], //: array [1..norw] of symbol;
  ssym = [], //: array [char] of symbol;
  mnemonic = [], //: array [fct] of packed array [1..5] of char;
  declbegsys, statbegsys, facbegsys, //: symset;
  table; //: array [0..txmax] of
  //  record name: alfa;
  //    case kind: object1 of
  //    constant: (val: integer);
  //    varible, proc: (level, adr, numargs: integer);
  //    vararr: (levela,adra,length: integer)
  //    /*instream & outstream have no fields*/
  // end;

// Start of utility routines for JS version

var unprocessedSource; // pl/0 processor nibbles away at beginning of input text

function textStream(initVal) { // closure for processing string as a stream
  var restOfString;

  var funcs = {
    eos: function() {
      return restOfString == "";
    },
    eoln: function() {
      if (funcs.eos())
        throw ("eoln with empty string");
      return restOfString.charAt(0) == '\n';
    },
    firstch: function() {
      var ch;

      if (funcs.eos())
        throw ("firstch with empty string");
      return restOfString.charAt(0);
    },
    readch: function() {
      var ch;

      if (funcs.eos())
        throw ("readch with empty string");
      ch = restOfString.charAt(0);
      restOfString = restOfString.slice(1);
      return ch;
    }
  };
  restOfString = initVal;
  return funcs;
}

// Object properties, with the value true, are a quick-and-dirty substitute for
// Pascal sets.  Missing properties, e.g. set[missingName], will give undefined as
// a falsy value.

function unionProps(x, y) {
  var workSet;

  function copyProps(z) {
    var propName;

    for (propName in z)
      workSet[propName] = z[propName];
  }

  workSet = {};
  copyProps(x);
  copyProps(y);
  return workSet;
}

function constructSet() {
  var newSet, i;
  newSet = {};
  for (i = 0; i < arguments.length; i++)
    newSet[arguments[i]] = true;
  return newSet;
}

function error(n /*: integer*/ ) {
  // Included error strings from p. 323 in Algs+DS=Programs
  var i, mesg = [];
  mesg[1] = "Use = instead of :=.";
  mesg[2] = "= must be followed by a number.";
  mesg[3] = "Identifier must be followed by =.";
  mesg[4] = "const, var, procedure must be followed by an identifier.";
  mesg[5] = "Semicolon or comma missing.";
  mesg[6] = "Incorrect symbol after statement part in block.";
  mesg[7] = "Statement expected.";
  mesg[8] = "Incorrect symbol after statement part in block.";
  mesg[9] = "Period expected.";
  mesg[10] = "Semicolon between statements is missing.";
  mesg[11] = "Undeclared identifier.";
  mesg[12] = "Assignment to constant or procedure is not allowed.";
  mesg[13] = "Assignment operator := expected.";
  mesg[14] = "call must be followed by an identifier.";
  mesg[15] = "Call of a constant or a variable is meaningless.";
  mesg[16] = "then expected.";
  mesg[17] = "Semicolon or end expected.";
  mesg[18] = "do expected.";
  mesg[19] = "Incorrect symbol following statement.";
  mesg[20] = "Relational operator expected.";
  mesg[21] = "Expression must not contain a procedure identifier.";
  mesg[22] = "Right parenthesis missing.";
  mesg[23] = "The preceding factor cannot be followed by this symbol.";
  mesg[24] = "An expression cannot begin with this symbol.";
  mesg[25] = "Incorrect number of arguments";
  mesg[30] = "This number is too large.";
  mesg[31] = "Incorrect array dim.";
  mesg[32] = "Argument identifier expected";
  mesg[33] = "{ expected";
  mesg[34] = "} expected";
  mesg[35] = "too much procedure nesting";

  listingbox.innerHTML += " ***";
  for (i = 0; i < cc - 1; i++)
    listingbox.innerHTML += " ";
  listingbox.innerHTML += "^" + n + " " + mesg[n] + "\n";
  listingbox.scrollTop = 99999;
  err = err + 1;

  // Jan 7, 2015
  if (err == 1) { // Should make correcting PL/0 code a little easier
    sourcebox.focus();
    sourcebox.setSelectionRange(symbolStart, symbolEnd + 1);
  }
} /*error*/

function formatNumber(num, len) {
  // Needed for outputting neatly.
  var work;

  work = String(num);
  while (work.length < len)
    work = " " + work;
  return work;
}

// End of utility routines

var getsym = (function () { // Immediately-invoked function expression
var commentLatency = 0;     // Needed for error token highlighting, protected in closure

return function () { // getsym - Gets token
  var i, j, k /*: integer*/ ;

  function getch() { // Handles whitespace for scanner
    if (cc == ll) {
      if (unprocessedSource.eos()) {
        sym = undefined;
        throw 'program incomplete';
      }
      getchPosition += commentLatency; // Record latency (# of comment chars in prev line)
      commentLatency = 0;
      ll = 0;
      cc = 0;
      listingbox.innerHTML += formatNumber(cx, 5) + ' ';
      // If a \ is detected, the rest of the line is a comment
      while (!unprocessedSource.eos() && unprocessedSource.firstch() != '\n'
      && unprocessedSource.firstch() != '\\') {
        ll = ll + 1;
        ch = unprocessedSource.readch();
        listingbox.innerHTML += ch;
        line[ll] = ch;
      }
      // Copy comment text to listing, but don't tokenize
      if (!unprocessedSource.eos() && unprocessedSource.firstch() == '\\')
        while (!unprocessedSource.eos() && unprocessedSource.firstch() != '\n') {
          commentLatency++; // latency for the present line
          ch = unprocessedSource.readch();
          listingbox.innerHTML += ch;
        }
      listingbox.innerHTML += '\n';
      listingbox.scrollTop = 99999;
      if (!unprocessedSource.eos())
        unprocessedSource.readch();
      ll = ll + 1;
      line[ll] = ' ';
    }
    cc = cc + 1;
    ch = line[cc];
    getchPosition++; // Jan 7, 2015
  } /*end getch*/

  /*begin getsym*/
  while (ch == ' ')
    getch();
  symbolStart = getchPosition - 1; // Jan 7, 2015
  if (ch >= 'a' && ch <= 'z') {
    // identifier or reserved word
    a = '';
    do {
      a += ch;
      symbolEnd = getchPosition - 1; // Jan 7, 2015
      getch();
    } while (ch >= 'a' && ch <= 'z' || ch >= '0' && ch <= '9');

    id = a;
    // Binary search of reserved word table
    i = 1;
    j = norw;
    do {
      k = ((i + j) / 2) | 0;
      if (id <= word[k])
        j = k - 1;
      if (id >= word[k])
        i = k + 1;
    } while (i <= j);
    if (i - 1 > j)
      sym = wsym[k];
    else
      sym = ident;
  }
  else if (ch >= '0' && ch <= '9') {
    //number
    k = 0;
    num = 0;
    sym = number;
    do {
      num = 10 * num + (ch - '0');
      symbolEnd = getchPosition - 1; // Jan 7, 2015
      k = k + 1;
      getch();
    } while (ch >= '0' && ch <= '9');

    if (k > kmax || num > nmax) {
      error(30);
      num = 0; /*BPW - so error is reported once*/
    }
  }
  else if (ch == ':') {
    symbolEnd = getchPosition - 1; // Jan 7, 2015
    getch();
    if (ch == '=') {
      sym = becomes;
      symbolEnd = getchPosition - 1; // Jan 7, 2015
      getch();
    }
    else
      sym = colon;
  }
  else {
    sym = ssym[ch];
    if (sym == undefined) {
      //listingbox.innerHTML += ch + ' outside character set';
      //listingbox.scrollTop = 99999;
      throw ch + ' outside character set';
    }
    symbolEnd = getchPosition - 1; // Jan 7, 2015
    getch();
  }
}; /*end getsym*/
})(); // end of iife

function gen(x /*: fct;*/ , y, z /*: integer*/, comment ) {
  // Saves generated instruction
  code[cx] = {};
  code[cx].f = x;
  code[cx].l = y;
  code[cx].a = z;
  if (comment!=undefined)
    code[cx].comment = comment;
  cx++;
} /*gen*/

function test(s1, s2, /*: symset;*/ n /*: integer*/ ) {
  // Wirth's compile error continuation scheme
  if (!s1[sym]) {
    error(n);
    while (!s1[sym] && !s2[sym])
      getsym();
  }
} /*test*/

function block(lev, tx, /*: integer;*/ fsys /*: symset*/ ) {
  // Compiles "block" syntactic unit
  var dx, //: integer;     /*data allocation index*/
    tx0, //: integer;     /*initial table index*/
    cx0, //: integer;     /*initial code index*/
    arrScanIndex; //:integer

  function enter(k /*: object1*/ ) { /*enter object1 into table*/
    tx++;
    table[tx] = {};
    table[tx].name = id;
    table[tx].kind = k;
    switch (k) {
      case constant:
        if (num > nmax) { //BPW - shouldn't happen!
          error(30);
          num = 0;
        }
        table[tx].val = num;
        break;
      case varible:
        table[tx].level = lev;
        table[tx].adr = dx;
        dx++;
        break;
      case vararr:
        table[tx].levela = lev;
        table[tx].adra = dx;
        // dx modified in vardeclaration
        break;
      case proc:
        table[tx].level = lev;
        break;
      default:
        //listingbox.innerHTML += ' bad k in enter()';
        //listingbox.scrollTop = 99999;
        throw 'bad k in enter()';
        /* shouldn't be called for instream or outstream */
    }
  } /*enter*/

  function position(id /*: alfa */ ) {
    // find identifier id in table and return subscript
    var i;
    table[0].name = id; // Sentinel position for simple linear search
    i = tx;
    while (table[i].name != id)
      i--;
    return i;
  }

  function constdeclaration() {
    // Stores a simple named constant to associate with a given number
    if (sym == ident)
    {
      getsym();
      if (sym == eql || sym == becomes) {
        if (sym == becomes)
          error(1);
        getsym();
        if (sym == number) {
          enter(constant);
          getsym();
        }
        else
          error(2);
      }
      else
        error(3);
    }
    else
      error(4);
  }

  function vardeclaration() {
    // integer variable or integer arrays
    var i;

    if (sym == ident) {
      getsym();
      if (sym == lbrac) {
        enter(vararr);
        getsym();
        if (sym == ident) {
          i = position(id);
          if (i == 0)
            error(11);
          else if (table[i].kind != constant)
            error(31);
          else
            table[tx].length = table[i].val;
        }
        else if (sym == number)
          table[tx].length = num;
        else
          error(31);
        if (table[tx].length < 1)
          error(31);
        else
        // Increase dx by number of stack slots needed at
        // runtime.  Includes space for length value
        // for subscript range checking
          dx += table[tx].length + 1;
        getsym();
        if (sym == rbrac)
          getsym();
        else
          error(22);
      }
      else
        enter(varible);
    }
    else
      error(4);
  }

  function listcode(start) { /*list code generated for this block*/
    var i;
    for (i = start; i < cx; i++) {
      listingbox.innerHTML +=
        formatNumber(i, 5) + " " + mnemonic[code[i].f] + " " +
        formatNumber(code[i].l, 3) + " " + formatNumber(code[i].a, 5) + " "+
          (code[i].comment==undefined ? "" : code[i].comment)+
          "\n";
    }
    listingbox.scrollTop = 99999;
  }

  function statement(fsys /*: symset*/ ) {
    var i, cx1, cx2, argcount /*: integer*/ ;

    function expression(fsys /*: symset*/ ) {
      // Classic expression grammar
      var addop /*: symbol*/ ;

      function term(fsys /*: symset*/ ) {
        var mulop /*: symbol*/ ;

        function factor(fsys /*: symset*/ ) {
          var i;

          test(facbegsys, fsys, 24);
          while (facbegsys[sym]) {
            if (sym == ident) {
              i = position(id);
              if (i == 0)
                error(11);
              else
                switch (table[i].kind) {
                  case constant:
                    gen(lit, 0, table[i].val);
                    break;
                  case varible:
                    gen(lod, lev - table[i].level, table[i].adr, table[i].name);
                    break;
                  case vararr:
                    getsym();
                    if (sym != lbrac)
                      error(33);
                    else
                      getsym();
                    expression(unionProps(constructSet(rbrac), fsys));
                    if (sym != rbrac)
                      error(34);
                    gen(lda, lev - table[i].levela, table[i].adra, table[i].name);
                    break;
                  case proc:
                    error(21);
                    break;
                  case instream:
                    gen(rdi, 0, 0);
                    break;
                  case outstream:
                    error(21);
                    break;
                  default:
                    //listingbox.innerHTML += ' bad kind in factor()';
                    //listingbox.scrollTop = 99999;
                    throw 'bad kind in factor()';
                }
              getsym();
            }
            else if (sym == number) {
              if (num > nmax) /*BPW - shouldn't happen*/
              {
                error(30);
                num = 0;
              }
              gen(lit, 0, num);
              getsym();
            }
            else if (sym == lparen) {
              getsym();
              expression(unionProps(constructSet(rparen), fsys));
              if (sym == rparen)
                getsym();
              else
                error(22);
            }
            test(fsys, constructSet(lparen), 23);
          }
        } /*end factor*/

        /*begin term*/
        factor(unionProps(constructSet(times, slash), fsys));
        while (sym == times || sym == slash) {
          mulop = sym;
          getsym();
          factor(unionProps(constructSet(times, slash), fsys));
          if (mulop == times)
            gen(opr, 0, 4, "*");
          else
            gen(opr, 0, 5, "/");
        }
      } /*end term*/

      /*begin expression*/
      if (sym == plus || sym == minus) {
        addop = sym;
        getsym();
        term(unionProps(constructSet(plus, minus), fsys));
        if (addop == minus)
          gen(opr, 0, 1, "negate");
      }
      else
        term(unionProps(constructSet(plus, minus), fsys));
      while (sym == plus || sym == minus) {
        addop = sym;
        getsym();
        term(unionProps(constructSet(plus, minus), fsys));
        if (addop == plus)
          gen(opr, 0, 2, "+");
        else
          gen(opr, 0, 3, "-");
      }
    } /*end expression*/

    function condition(fsys /*: symset*/ ) {
      var relop /*: symbol*/ ;

      if (sym == oddsym) {
        getsym();
        expression(fsys);
        gen(opr, 0, 6, "odd");
      }
      else {
        expression(unionProps(constructSet(eql, neq, lss, gtr, leq, geq), fsys));

        if (sym != eql && sym != neq && sym != lss && sym != leq
        && sym != gtr && sym != geq)
          error(20);
        else {
          relop = sym;
          getsym();
          expression(unionProps(constructSet(eql, neq, lss, gtr, leq, geq), fsys));
          switch (relop) {
            case eql:
              gen(opr, 0, 8, "=");
              break;
            case neq:
              gen(opr, 0, 9, "#");
              break;
            case lss:
              gen(opr, 0, 10, "<");
              break;
            case geq:
              gen(opr, 0, 11, "]");
              break;
            case gtr:
              gen(opr, 0, 12, ">");
              break;
            case leq:
              gen(opr, 0, 13, "[");
              break;
            default:
              //listingbox.innerHTML += ' bad relop in condition()';
              //listingbox.scrollTop = 99999;
              throw 'bad relop in condition()';
          }
        }
      }
    } /*end condition*/

    /*begin statement*/
    if (sym == ident) { // assignment statement
      i = position(id);
      if (i == 0)
        error(11);
      else if (table[i].kind != varible && table[i].kind != vararr 
      && table[i].kind != outstream) {
        /*assignment to non-varible*/
        error(12);
        i = 0;
      }
      getsym();
      if (table[i].kind == vararr)
        if (sym == lbrac) { // subscripting
          getsym();
          expression(unionProps(constructSet(rbrac), fsys));
          if (sym == rbrac)
            getsym();
          else
            error(22);
        }
        else
          error(21);
      if (sym == becomes)
        getsym();
      else
        error(13);
      expression(fsys);
      if (i != 0)
        if (table[i].kind == varible)
          gen(sto, lev - table[i].level, table[i].adr, table[i].name);
        else if (table[i].kind == vararr)
          gen(sta, lev - table[i].levela, table[i].adra, table[i].name)
        else
          gen(wro, 0, 0) /*for outstream*/
    }
    else if (sym == callsym) {
      getsym();
      if (sym != ident)
        error(14);
      else {
        i = position(id);
        if (i == 0)
          error(11);
        // code for passing args by value, arrays may not be passed
        getsym();
        if (table[i].kind != proc)
          error(15);
        else if (table[i].numargs == 0)
          gen(cal, lev - table[i].level, table[i].adr, table[i].name);
        else if (sym == lparen) {
          // Position of first parameter in new activation record
          // after s.l., d.l., and return address
          gen(int, 0, 3, "push args(s) for "+table[i].name); 
          argcount = 0;
          do { // Code to place argument expression values on stack
            argcount++;
            getsym();
            expression(unionProps(constructSet(comma, rparen), fsys));
            test(constructSet(comma, rparen), fsys, 19);
          } while (sym == comma);
          if (table[i].numargs == argcount) {
            // back to start of new activation record
            gen(int, 0, -argcount - 3, "-(3+number of args)");
            gen(cal, lev - table[i].level, table[i].adr, table[i].name);
          }
          else
            error(25);
          getsym();
        }
        else
          error(19);
      }
    }
    else if (sym == ifsym) { // Adds "else" to PL/0
      getsym();
      condition(unionProps(constructSet(thensym, dosym), fsys));
      if (sym == thensym)
        getsym();
      else
        error(16);
      cx1 = cx;
      gen(jpc, 0, 0);
      statement(unionProps(constructSet(elsesym), fsys));
      if (sym == elsesym) {
        getsym();
        cx2 = cx;
        gen(jmp, 0, 0);
        code[cx1].a = cx;
        statement(fsys);
        code[cx2].a = cx;
      }
      else
        code[cx1].a = cx;
    }
    else if (sym == beginsym) {
      getsym();
      statement(unionProps(constructSet(semicolon, endsym), fsys));
      while (sym == semicolon || statbegsys[sym]) {
        if (sym == semicolon)
          getsym();
        else
          error(10);
        statement(unionProps(constructSet(semicolon, endsym), fsys));
      }
      if (sym == endsym)
        getsym();
      else
        error(17);
    }
    else if (sym == whilesym) {
      cx1 = cx;
      getsym();
      condition(unionProps(constructSet(dosym), fsys));
      cx2 = cx;
      gen(jpc, 0, 0);
      if (sym == dosym)
        getsym();
      else
        error(18);
      statement(fsys);
      gen(jmp, 0, cx1);
      code[cx2].a = cx;
    }
    test(fsys, {}, 19);
  } /*end statement*/

  /*begin block*/
  dx = 3;
  tx0 = tx;
  table[tx].adr = cx;
  gen(jmp, 0, 0);
  if (lev > levmax)
    error(35);
  if (lev > 0) { // have procedure header, so deal w/ parameter names
    table[tx].numargs = 0;
    if (sym == lparen) {
      do {
        getsym();
        if (sym == ident) {
          enter(varible);
          table[tx0].numargs++;
          getsym();
        }
        else
          error(32);
        test(constructSet(comma, rparen), fsys, 19);
      } while (sym == comma);
      getsym();
    }
    if (sym == semicolon)
      getsym();
    else
      error(5);
  }
  else
    dx = 8; // allow RTS space for cvx,cvy,cvclickx,cvclicky,emojicount

  do { // This loop exists only to help with Wirth's error handling scheme.
    if (sym == constsym) {
      getsym();
      do {
        constdeclaration();
        while (sym == comma) {
          getsym();
          constdeclaration();
        }
        if (sym == semicolon) {
          getsym();
          break; // Patched Jan 7, 2015 to prevent compiling const a=3;b=4;
        }
        else
          error(5);
      }
      while (sym == ident);
    }
    if (sym == varsym) {
      getsym();
      do {
        vardeclaration();
        while (sym == comma) {
          getsym();
          vardeclaration();
        }
        if (sym == semicolon) {
          getsym();
          break; // Patched Jan 7, 2015 to prevent compiling var x;y;z;
        }
        else
          error(5);
      }
      while (sym == ident);
    }
    while (sym == procsym) {
      getsym();
      if (sym == ident) {
        enter(proc);
        getsym();
      }
      else
        error(4);
      /* Moved earlier in block due to parameter handling
      if (sym == semicolon)
         getsym();
      else
         error(5);
      */
      block(lev + 1, tx, unionProps(constructSet(semicolon), fsys));
      if (sym == semicolon) {
        getsym();
        test(unionProps(constructSet(ident, procsym), statbegsys), fsys, 6);
      }
      else
        error(5);
    }
    test(unionProps(constructSet(ident), statbegsys), declbegsys, 7);
  }
  while (declbegsys[sym]);
  code[table[tx0].adr].a = cx;
  table[tx0].adr = cx; /*start adr of code*/
  cx0 = cx;
  gen(int, 0, dx, "code for "+table[tx0].name);
  // For use by dumpRTS() in interpret()
  code[cx0].table=[];
  for (var tableIndex = tx0; tableIndex<=tx; tableIndex++)
    if (table[tableIndex].kind==varible || table[tableIndex].kind==vararr)
      code[cx0].table.push(table[tableIndex]);

  // Set up array indexing
  for (arrScanIndex = tx0 + 1; arrScanIndex <= tx; arrScanIndex++)
    if (table[arrScanIndex].kind == vararr) {
      gen(lit, 0, table[arrScanIndex].length, "array " + table[arrScanIndex].name
        + " length");
      //gen(sto, table[arrScanIndex].levela, table[arrScanIndex].adra);
      gen(sto, 0, table[arrScanIndex].adra, "saved before element 0"); // patch
    }

  statement(unionProps(constructSet(semicolon, endsym), fsys));
  gen(opr, 0, 0, "return");
  test(fsys, {}, 8);
  if (err == 0) {
    listcode(cx0);
    listingbox.innerHTML += "\n";
    if (lev == 0)
      listcode(0);
  }
} /*end block*/

var interpret; // Gets function for closure created by initMachine
var dumpRTSclosure; // Gets function for closure created by initMachine

function initMachine() {
  var stacksize = 5000,
    p, b, t, // program-, base-, topstack-registers
    i, // instruction register
    s = [], // datastore
    sIndex,
    unprocessedNumbers = textStream(instreambox.value),
    inOpen = true, str, ch, num, sign; // number input through in stream
  var emoji;
  var dumpComment = []; // parallel array to s
  var stepcount=0; // Moved here to correct false resets.
  function base(l) { // Handles lexical scoping by traversing
  // static links.  See notes 05 and Gabbrielli 5.5.1, p. 105
    var b1 = b;
    while (l > 0) {
      b1 = s[b1];
      l--;
    }
    return b1;
  }

  function ord(x) { // maps boolean to a number
    return x ? 1 : 0;
  }

  function odd(x) {
    return Math.abs(x) % 2 == 1;
  }

  /* initMachine */
  outstreambox.innerHTML = "start pl/0\n";
  t = 0;
  b = 1;
  p = 0;
  for (sIndex = 1; sIndex <= stacksize; sIndex++)
    s[sIndex] = 0;

  s[4] = -999999; s[5] = -999999; // cvx and cvy
  s[6] = -999999; s[7] = -999999; // cvclickx and cvclicky
  emoji = emojibox.value;
  while (emoji.length%2 == 1)
    emoji = prompt("Please fix emoji string", emoji);
  emojibox.value = emoji;
  s[8] = emoji.length/2; // emojicount
  dumpComment[4] = "cvx"; dumpComment[5] = "cvy";
  dumpComment[6] = "cvclickx"; dumpComment[7] = "cvclicky";  
  dumpComment[8] = "emojicount";
  cvxcvybox.innerHTML = "-999999 -999999";
  canvas.onmousemove =
    function(evt) {
      var loc = getPosition(evt);
      s[4] = loc.x; s[5] = loc.y;
      cvxcvybox.innerHTML = loc.x + ' ' + loc.y;
    };
  canvas.onmouseout =
    function() {
      s[4] = -999999; s[5] = -999999;
      cvxcvybox.innerHTML = "-999999 -999999";
    };

  interpret = function() { // Closure created
    var steplimit; //, stepcount; Moved to initMachine Feb 8, 2015
    var unprocessedBkpts, breakpoint = [];
    function dumpRTS() {
      // Dump rts using the temp RTSout to avoid costly getter/setter 
      // access to rtsbox.innerHTML
      var rtsIndex, nextBase, RTSout;
      var nTemp = b;
      RTSout = "b=" + b + " p=" + p;
      nextBase = b;
      for (rtsIndex = t; rtsIndex > 0; rtsIndex--) {
        RTSout += "\n" + formatNumber(rtsIndex, 4) + " "
                  + formatNumber(s[rtsIndex], 8);
        if (rtsIndex == nextBase) {
          RTSout += " s.l.";
          if(nTemp == rtsIndex) {
          RTSout += "\n**********************";
          nTemp = s[rtsIndex];
      }
          nextBase = s[rtsIndex + 1]; // dynamic link has beginning of caller frame
        }
        else if (rtsIndex == nextBase + 1)
          RTSout += " d.l.";
        else if (rtsIndex == nextBase + 2)
          RTSout += " ret adr";
        else if (dumpComment[rtsIndex])
          RTSout += " " + dumpComment[rtsIndex];
      }
      rtsbox.innerHTML = RTSout;
      rtsbox.scrollTop = 1;

    }

    dumpRTSclosure=dumpRTS; // So hitting stop button can produce dump

    function doInstructions() {
      var arrPos, length, rval, index, fontsave;

      try {
        do {
          // Stop if p is marked as breakpoint and at least one step has occured.
          if (stepcount > 0 && breakpoint[p])
            break;
          stepcount++;
          i = code[p];
          if(i.f != 7)
          	coveredCode[p].symbol = "***";
          
          p++;
          // Removed the confusing "with" in the Pascal version
          switch (i.f) {
            case lit:
              s[++t] = i.a;
              break;
            case opr:
              switch (i.a) { // operator
                case 0: // return from procedure
                  t = b - 1;
                  dumpComment.length = t + 1; // discard irrelevant comments
                  p = s[t + 3];
                  b = s[t + 2];
                  //nishant
                  // if(b == 1)
                  // 	dumpRTS();
                  break;
                case 1:
                  s[t] = -s[t];
                  break;
                case 2:
                  t--;
                  s[t] = s[t] + s[t + 1];
                  break;
                case 3:
                  t--;
                  s[t] = s[t] - s[t + 1];
                  break;
                case 4:
                  t--;
                  s[t] = s[t] * s[t + 1];
                  break;
                case 5:
                  t--;
                  s[t] = (s[t] / s[t + 1]) | 0; // integer divide
                  break;
                case 6:
                  s[t] = ord(odd(s[t]));
                  break;
                case 8:
                  t--;
                  s[t] = ord(s[t] == s[t + 1]);
                  break;
                case 9:
                  t--;
                  s[t] = ord(s[t] != s[t + 1]);
                  break;
                case 10:
                  t--;
                  s[t] = ord(s[t] < s[t + 1]);
                  break;
                case 11:
                  t--;
                  s[t] = ord(s[t] >= s[t + 1]);
                  break;
                case 12:
                  t--;
                  s[t] = ord(s[t] > s[t + 1]);
                  break;
                case 13:
                  t--;
                  s[t] = ord(s[t] <= s[t + 1]);
                  break;
              } // end of switch
              break;
            case lod:
              s[++t] = s[base(i.l) + i.a];
              break;
            case sto:
              s[base(i.l) + i.a] = s[t--];
              break;
            case lda:
              arrPos = base(i.l) + i.a;
              length = s[arrPos];
              arrPos = arrPos + 1;
              index = s[t]; // computed subscript value
              if (index < 0 || index >= length)
                throw 'index abort at p=' + (p - 1);
              s[t] = s[arrPos + index];
              break;
            case sta:
              arrPos = base(i.l) + i.a;
              length = s[arrPos];
              arrPos = arrPos + 1;
              rval = s[t--];  // value to be stored in array
              index = s[t--]; // computed subscript value
              if (index < 0 || index >= length)
                throw 'index abort at p=' + (p - 1);
              s[arrPos + index] = rval;
              break;
            case cal: // generate new block mark
              s[t + 1] = base(i.l);
              s[t + 2] = b;
              s[t + 3] = p;
              b = t + 1;
              p = i.a;
              if (p < 0) { // Intrinsic function
                switch (p) {
                  case -1: // cvclear
                    ctx.clearRect(0, 0, graphic.width, graphic.height);
                    break;
                  case -2: // cvball
                    ctx.beginPath();
                    ctx.arc(s[b + 3], s[b + 4], s[b + 5], 0, Math.PI * 2)
                    ctx.closePath();
                    ctx.fillStyle = "red";
                    ctx.fill();
                    break;
                  case -3: // cvdraw
                    ctx.drawImage(pic[s[b + 3]], s[b + 4], s[b + 5], 
                      s[b + 6], s[b + 7]);
                    break;
                  case -4: // wait k milliseconds for JS to continue
                    // restart may be blocked by clearTimeout()
                    timeOutID = setTimeout(doInstructions, s[b + 3]);
                    t = b - 1;
                    p = s[t + 3];
                    b = s[t + 2];
                    return;
                  case -5: // cvline
                    ctx.beginPath();
                    ctx.strokeStyle = "black";
                    ctx.lineWidth = 1;
                    ctx.moveTo(s[b + 3], s[b + 4]);
                    ctx.lineTo(s[b + 5], s[b + 6]);
                    ctx.stroke();
                    break;
                  case -6: // cvbox
                    ctx.beginPath();
                    ctx.fillStyle = "blue";
                    ctx.rect(s[b + 3], s[b + 4], s[b + 5], s[b + 6]);
                    ctx.fill();
                    break;
                  case -7: // stop
                    suspendInterpreter();
                    t = b - 1;
                    p = s[t + 3];
                    b = s[t + 2];
                    dumpRTS();
                    return;
                  case -8: // die    
                    t = b - 1;
                    p = s[t + 3];
                    b = s[t + 2];
                    throw "call to die";
                  case -9: // cvclick
                    t = b - 1;
                    p = s[t + 3] - 1; // Just in case of stop, editing, or break
                    b = s[t + 2];
                    if (canvas.onclick || cvasclickFlag)
                      throw "cvclick with cvasclick active!!! ";
                    canvas.style.cursor = "help";
                    canvas.onclick =
                      function() {
                        canvas.style.cursor = "pointer";
                        canvas.onclick = undefined; // Don't leave handler around!
                        p++; // Have click, so continue with next instruction
                        // doinstructions is called in this handler, since changes
                        // in breakpoints should wait until the interpreter is
                        // stopped at the PL/0 abstraction level.
                        doInstructions();
                      };
                    return; // Suspends interpreter until click on canvas
                  case -10: // cvtriangle
                    ctx.beginPath();
                    ctx.fillStyle = "green";
                    ctx.moveTo(s[b + 3], s[b + 4]);
                    ctx.lineTo(s[b + 5], s[b + 6]);
                    ctx.lineTo(s[b + 7], s[b + 8]);
                    ctx.closePath();
                    ctx.fill();
                    break;
                  case -11: // cvtext
                    ctx.textAlign="center";
                    ctx.textBaseline="middle";
                    ctx.fillStyle = "black";
                    ctx.fillText(s[b + 3], s[b + 4], s[b + 5]);
                    break;
                  case -12: // cvasclick
                    if (canvas.onclick)
                      alert("cvasclick with cvasclick already active!!!");
                    else {
                      canvas.style.cursor = "crosshair";
                      s[6] = -999999;
                      s[7] = -999999;
                      canvas.onclick = 
                        function(evt) { // Click will be handled after a wait() occurs
                          var loc = getPosition(evt);
                          canvas.style.cursor = "pointer";
                          canvas.onclick = undefined; // Don't leave handler around!
                          // Avoid accidental restore of handler after suspend
                          cvasclickFlag = false;
                          if (envState != stopState) {
                            alert("canvas.onclick for cvasclick when envState= "
                              + envState);
                            return;
                          }
                          s[6] = loc.x;
                          s[7] = loc.y;
                        };
                      cvasclickFlag = true;
                    }                   
                    break;
                  case -13: // emojidraw(emoji#,x,y,size)
                    if (s[b + 3] < 1 || s[b + 3] > s[8]) // s[8] is emojicount
                      throw "emojidraw - range error " + s[b + 3];
                    fontsave = ctx.font;
                    ctx.textAlign="center";
                    ctx.textBaseline="middle";
                    ctx.fillStyle = "black";
                    ctx.font = s[b + 6] + "px Courier";
                    ctx.fillText(emoji.slice(2 * (s[b + 3] - 1),
                                             2 * s[b + 3]),
                                 s[b + 4], s[b + 5]);
                    ctx.font = fontsave;
                    break;
                }
                t = b - 1;    // return from intrinsic
                p = s[t + 3];
                b = s[t + 2];
              } // end intrinsic function
              break;
            case int:
              t += i.a;
              // Set up the RTS dump with names of variables in new stack frame
              if (i.table) {
                for (var tabIndex = 0; tabIndex < i.table.length; tabIndex++)
                  if (i.table[tabIndex].kind == varible)
                    dumpComment[b + i.table[tabIndex].adr] = i.table[tabIndex].name;
                  else if (i.table[tabIndex].kind == vararr) {
                    dumpComment[b + i.table[tabIndex].adra] = i.table[tabIndex].name
                                                             + " length";
                    for (var subIndex = 0; 
                             subIndex < i.table[tabIndex].length; 
                             subIndex++)
                      dumpComment[b + i.table[tabIndex].adra + 1 + subIndex] =
                        i.table[tabIndex].name + "{" + subIndex + "}";
                  }
              }
              break;
            case jmp:
              p = i.a;
              break;
            case jpc:
              if (s[t--] == 0) {
              	if(coveredCodeBackup[p-1].symbol == "---")
              		coveredCode[p-1].symbol = "***";
              	else if(coveredCodeBackup[p-1].symbol != "***")
              		coveredCode[p - 1].symbol = "+++";
                p = i.a;
            }
            else {
            	if(coveredCodeBackup[p-1].symbol == "+++")
              		coveredCode[p-1].symbol = "***";
              	else if(coveredCodeBackup[p-1].symbol != "***")
              		coveredCode[p - 1].symbol = "---";
            }
              break;
            case rdi:
              if (!inOpen)
                throw "Input already terminated";
              // Numbers from instreambox
              try {
                while (true) {
                  if (unprocessedNumbers.eos())
                    throw "input exhausted";
                  ch = unprocessedNumbers.readch();
                  if (ch != ' ' && ch != '\n')
                    break;
                }
                sign = 1;
                if (ch == '-') {
                  sign = (-1);
                  do {
                    ch = unprocessedNumbers.readch();
                  } while (ch == ' ' || ch == '\n');
                }
                if (ch < '0' || ch > '9')
                  throw ch + " is not a digit";
                num = ch - '0';
                while (!unprocessedNumbers.eos() && !unprocessedNumbers.eoln() &&
                unprocessedNumbers.firstch() >= '0' && 
                unprocessedNumbers.firstch() <= '9') {
                  ch = unprocessedNumbers.readch();
                  num = 10 * num + (ch - '0');
                }
                num = sign * num;
              } // end of try
              catch (mesg) {
                if (mesg == "input exhausted")
                  num = (-999999);
                else
                  throw mesg;
              }
              s[++t] = num;
              inOpen = num != (-999999);
              break;
            case wro:
              outstreambox.innerHTML += s[t--] + "\n";
              outstreambox.scrollTop = 99999;
              break;
          } //end of switch
        } while (p != 0 && stepcount < steplimit && t <= stacksize); // end do
        if (p != 0) {
          suspendInterpreter();
          stepcount = 0; // Placed here Feb 8, 2015
        }
      }
      catch (exc) { 
        alert("(700) exception at p=" + p + " " + exc);
        terminateInterpreter();
      }

      if (t > stacksize) { 
        alert("(800) RTS overflow");
        terminateInterpreter();
      }
      if (p == 0) {
        outstreambox.innerHTML += "end pl/0";
        outstreambox.scrollTop = 99999;
        terminateInterpreter();
      }
    } // end doInstructions

    /* begin interpret */
    // Check for stepping
    if (steplimitbox.value == "")
      steplimit = 99999999999;
    else {
      steplimit = parseInt(steplimitbox.value);
      if (String(steplimit) != steplimitbox.value || steplimit < 1) {
        alert("(900) Fix step limit and hit Continue");
        return;
      }
    }

    // Check for breakpoints
    unprocessedBkpts = textStream(breakpointbox.value);
    while (true)
      try {
        while (true) {
          if (unprocessedBkpts.eos())
            throw "only whitespace";
          ch = unprocessedBkpts.readch();
          if (ch != ' ' && ch != '\n')
            break;
        }
        if (ch < '0' || ch > '9')
          throw ch + " in Breakpoints is not a digit";
        num = ch - '0';
        while (!unprocessedBkpts.eos() && !unprocessedBkpts.eoln() &&
          unprocessedBkpts.firstch() >= '0' && unprocessedBkpts.firstch() <= '9') {
          ch = unprocessedBkpts.readch();
          num = 10 * num + (ch - '0');
        }
        if (num < cx)
          breakpoint[num] = true;
        else
          alert("(1000) Meaningless breakpoint " + num + " ignored");
      }
    catch (mesg) {
      if (mesg != "only whitespace")
        alert("(1100) " + mesg);
      break;
    }

    // stepcount = 0; removed Feb 8, 2015
    doInstructions();
    listcoverage(0);
  }; // end interpret()
} // end initMachine()

function wrappedCompile() { // Triggered by compile button in html
  cvasclickFlag = false; // in case previous execution was sitting suspended
  coveragebox.innerHTML = "";
  coveredCodeBackup = [];
  // "else" has been added to Wirth's PL/0
  word[1] = 'begin';
  word[2] = 'call';
  word[3] = 'const';
  word[4] = 'do';
  word[5] = 'else';
  word[6] = 'end';
  word[7] = 'if';
  word[8] = 'odd';
  word[9] = 'procedure';
  word[10] = 'then';
  word[11] = 'var';
  word[12] = 'while';
  wsym[1] = beginsym;
  wsym[2] = callsym;
  wsym[3] = constsym;
  wsym[4] = dosym;
  wsym[5] = elsesym;
  wsym[6] = endsym;
  wsym[7] = ifsym;
  wsym[8] = oddsym;
  wsym[9] = procsym;
  wsym[10] = thensym;
  wsym[11] = varsym;
  wsym[12] = whilesym;
  // Other special characters are trapped in the scanner
  ssym['+'] = plus;
  ssym['-'] = minus;
  ssym['*'] = times;
  ssym['/'] = slash;
  ssym['('] = lparen;
  ssym[')'] = rparen;
  ssym['='] = eql;
  ssym[','] = comma;
  ssym['.'] = period;
  ssym['#'] = neq;
  ssym['<'] = lss;
  ssym['>'] = gtr;
  ssym['['] = leq;
  ssym[']'] = geq;
  ssym[';'] = semicolon;
  ssym[':'] = colon;
  ssym['{'] = lbrac;
  ssym['}'] = rbrac;
  mnemonic[lit] = '  lit';
  mnemonic[opr] = '  opr';
  mnemonic[lod] = '  lod';
  mnemonic[sto] = '  sto';
  mnemonic[cal] = '  cal';
  mnemonic[int] = '  int';
  mnemonic[jmp] = '  jmp';
  mnemonic[jpc] = '  jpc';
  mnemonic[rdi] = '  rdi';
  mnemonic[wro] = '  wro';
  mnemonic[lda] = '  lda';
  mnemonic[sta] = '  sta';
  declbegsys = constructSet(constsym, varsym, procsym);
  statbegsys = constructSet(beginsym, callsym, ifsym, whilesym);
  facbegsys = constructSet(ident, number, lparen);
  err = 0;
  cc = 0;
  cx = 0;
  ll = 0;
  ch = ' ';
  //kk = al; removed dec 2014
  getchPosition = 0; // Jan 7, 2015

  unprocessedSource = textStream(sourcebox.value);
  listingbox.innerHTML = "";
  getsym();
  table=[];
  table.push({}); // Used as sentinel for position searches
  // pre-load symbol table for names of intrinsics implemented in interpreter. 
  // for in and out streams
  table.push({
    name: 'in',
    kind: instream
  });

  table.push({
    name: 'out',
    kind: outstream
  });

  // graphic routines
  table.push({
    name: 'cvclear',
    kind: proc,
    level: 0,
    adr: -1,
    numargs: 0
  });

  table.push({
    name: 'cvball',
    kind: proc,
    level: 0,
    adr: -2,
    numargs: 3
  });

  table.push({
    name: 'cvdraw',
    kind: proc,
    level: 0,
    adr: -3,
    numargs: 5
  });

  // constant for number of pictures available to cvdraw
  table.push({
    name: 'imagemax',
    kind: constant,
    val: 3 // three images available
  });

  // wait a number of milliseconds
  table.push({
    name: 'wait',
    kind: proc,
    level: 0,
    adr: -4,
    numargs: 1
  });

  // mouse position over canvas, values supplied by canvas.onmousemove and
  // canvas.onmouseout
  table.push({
    name: 'cvx',
    kind: varible,
    level: 0,
    adr: 3 // store at s[4]
  });

  table.push({
    name: 'cvy',
    kind: varible,
    level: 0,
    adr: 4 // store at s[5]
  });

  // more graphics
  table.push({
    name: 'cvline',
    kind: proc,
    level: 0,
    adr: -5,
    numargs: 4
  });

  table.push({
    name: 'cvbox',
    kind: proc,
    level: 0,
    adr: -6,
    numargs: 4
  });

  // suspend interpreter
  table.push({
    name: 'stop',
    kind: proc,
    level: 0,
    adr: -7,
    numargs: 0
  });

  // kill interpreter
  table.push({
    name: 'die',
    kind: proc,
    level: 0,
    adr: -8,
    numargs: 0
  });

  // synchronous mouseclick
  table.push({
    name: 'cvclick',
    kind: proc,
    level: 0,
    adr: -9,
    numargs: 0
  });

  table.push({ // draw a green triangle
    name: 'cvtriangle',
    kind: proc,
    level: 0,
    adr: -10,
    numargs: 6
  });

  table.push({ // output a number as text at supplied coordinates
    name: 'cvtext',
    kind: proc,
    level: 0,
    adr: -11,
    numargs: 3
  });

  // synchronous mouseclick
  table.push({
    name: 'cvclickx',
    kind: varible,
    level: 0,
    adr: 5 // store at s[6]
  });

  table.push({
    name: 'cvclicky',
    kind: varible,
    level: 0,
    adr: 6 // store at s[7]
  });

  table.push({
    name: 'cvasclick',
    kind: proc,
    level: 0,
    adr: -12,
    numargs: 0
  });

  // displaying emoji on canvas
  table.push({
    name: 'emojicount',
    kind: varible,
    level: 0,
    adr: 7 // store at s[8]
  });

  table.push({
    name: 'emojidraw',
    kind: proc,
    level: 0,
    adr: -13,
    numargs: 4
  });

  table.push({name: "unnamed driver"}); // From Summer 13 Wirth bug

  block(0, table.length-1,
    unionProps(unionProps(constructSet(period), declbegsys), statbegsys));
}

function compile () {
  try
  {
    wrappedCompile();
  }
  catch (mesg)
  {
    listingbox.innerHTML += mesg+"\n";
    listingbox.scrollTop = 99999;
  }
  if (sym != period)
    error(9);
  compileButton.disabled = true;
  if (err == 0)
    compiledClean();
  else 
    compileError();
}
