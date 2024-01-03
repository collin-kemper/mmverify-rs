#![allow(nonstandard_style)]
use std::collections::{ HashMap, HashSet, };
use std::env;
use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;

/* -------------- tokens --------------- */
// TODO: make basic lexer
const TOK_EOF      : u8 = 0x00; /* end of file */
const TOK_WSP      : u8 = 0x01; /* whitespace */
const TOK_CONST    : u8 = 0x02; /* $c */
const TOK_VAR      : u8 = 0x03; /* $v */
const TOK_DISJOINT : u8 = 0x04; /* $d */
const TOK_FLOATING : u8 = 0x05; /* $f */
const TOK_ESSENTIAL: u8 = 0x06; /* $e */
const TOK_AXIOM    : u8 = 0x07; /* $a */
const TOK_PROOF    : u8 = 0x08; /* $p */
const TOK_EQ       : u8 = 0x09; /* $= */
const TOK_DOT      : u8 = 0x0a; /* $. */
const TOK_BLOCK_START: u8 = 0x0b; /* ${ */
const TOK_BLOCK_END: u8 = 0x0c; /* $} */

const ASCII_TAB: u8 = 0x09;
const ASCII_LF : u8 = 0x0a;
const ASCII_FF : u8 = 0x0c;
const ASCII_CR : u8 = 0x0d;
const ASCII_SP : u8 = 0x20;
const ASCII_LPAR : u8 = 0x28;
const ASCII_RPAR : u8 = 0x29;
const ASCII_DASH : u8 = 0x2d;
const ASCII_DOT  : u8 = 0x2e;
const ASCII_0    : u8 = 0x30;
const ASCII_9    : u8 = 0x39;
const ASCII_EQ   : u8 = 0x3d;
const ASCII_A    : u8 = 0x41;
const ASCII_Z    : u8 = 0x5a;
const ASCII_LSBR : u8 = 0x5b;
const ASCII_RSBR : u8 = 0x5d;
const ASCII_UND  : u8 = 0x5f;
const ASCII_a    : u8 = 0x61;
const ASCII_c    : u8 = 0x63;
const ASCII_d    : u8 = 0x64;
const ASCII_e    : u8 = 0x65;
const ASCII_f    : u8 = 0x66;
const ASCII_p    : u8 = 0x70;
const ASCII_v    : u8 = 0x76;
const ASCII_z    : u8 = 0x7a;
const ASCII_LCBR : u8 = 0x7b;
const ASCII_RCBR : u8 = 0x7d;

enum Tok {
  Char(u8),
  Eof,
  Err(std::io::Error),
}

/* the keywords are pretty simple, so */
struct TokReader {
  r: BufReader<File>,
}

impl TokReader {
  fn new(f: File) -> TokReader {
    return TokReader {
      r: BufReader::new(f),
    };
  }

  fn consume_comment(&mut self) {
    loop {
      let next_u8 = {
        let buf = self.r.fill_buf().unwrap();
        if buf.is_empty() {
          return;
        }
        buf[0]
      };
      self.r.consume(1);
      match next_u8 {
        ASCII_DOL => {
          let next_u8 = {
            let buf = self.r.fill_buf().unwrap();
            if buf.is_empty() {
              return;
            }
            buf[0]
          };
          self.r.consume(1);
          match next_u8 {
            ASCII_RPAR => return,
            _        => {},
          }
        },
        _ => continue,
        
      }
    }
  }

  fn next(&mut self) -> u8 {
    loop {
      let buf = self.r.fill_buf().unwrap();
      if !buf.is_empty() {
        let ret = buf[0];
        self.r.consume(1);
        match ret {
          ASCII_DOL => {
            /* peek ahead to see if its a comment or include */
            let buf = self.r.fill_buf().unwrap();
            if buf.is_empty() {
              panic!("invalid");
            } else {
              self.r.consume(1);
              match buf[0] {
                ASCII_LPAR => self.consume_comment(),
                ASCII_DOT  => return TOK_DOT,
                ASCII_EQ   => return TOK_EQ,
                ASCII_a    => return TOK_AXIOM,
                ASCII_c    => return TOK_CONST,
                ASCII_d    => return TOK_DISJOINT,
                ASCII_e    => return TOK_ESSENTIAL,
                ASCII_f    => return TOK_FLOATING,
                ASCII_p    => return TOK_PROOF,
                ASCII_v    => return TOK_VAR,
                ASCII_LCBR => return TOK_BLOCK_START,
                ASCII_RCBR => return TOK_BLOCK_END,
                _          => panic!("invalid"),
              }
            }
            // let buf = self.r.fill_buf().unwrap();
            // if buf.is_empty() {
            //   // print!("{}", ret as char);
            //   // std::io::stdout().flush().unwrap();
            //   // print!("{:02x}", ret);
            //   return ret;
            // } else {
            //   match buf[0] {
            //     TOK_LPAR => {
            //       self.r.consume(1);
            //       self.consume_comment();
            //       continue;
            //     },
            //     TOK_LSBR => panic!("not implemented"),
            //     _ => {
            //       // print!("{:02x}", ret);
            //       // print!("{}", ret as char);
            //       // std::io::stdout().flush().unwrap();
            //       return ret;
            //     },
            //   }
            // }
          },
          ASCII_TAB|ASCII_LF|ASCII_FF|ASCII_CR|ASCII_SP => return TOK_WSP,
          _ => {
            // print!("{:02x}", ret);
            // print!("{}", ret as char);
            // std::io::stdout().flush().unwrap();
            return ret;
          },
        }
      } else {
        // print!("<EOF>");
        return 0x00;
      }
    }
  }
}

#[derive(PartialEq, Eq, Clone)]
enum SymbolType {
  Var,
  Const,
  Hyp,
  Assert,
}

#[derive(PartialEq, Eq, Clone)]
struct Symbol {
  t: SymbolType,
  id: u32,
}

#[derive(Clone)]
struct SymStr {
  t: u32,
  syms: Vec<Symbol>,
}

#[derive(Clone)]
enum Hypothesis {
  F { t: u32, var: u32 },
  E(SymStr),
}

struct Assertion {
  hyps: Vec<Hypothesis>,
  consequent: SymStr,
  disjoint_vars: HashSet<(u32, u32)>,
}

struct Parser {
  r: TokReader,

  // symbols and data
  sym_map:       HashMap<Vec<u8>, Symbol>,
  var_count: u32,
  const_count: u32,
  hyps: Vec<Hypothesis>,
  asserts: Vec<Assertion>,

  // proof state?
  stack:         Vec<SymStr>,
  disjoint_vars: HashSet<(u32, u32)>,
}

impl Parser {
  fn new(fname: &String) -> std::io::Result<Parser> {
    let f = File::open(fname)?;
    let r = TokReader::new(f);
    Ok(Parser {
      r: r,

      sym_map:     HashMap::new(),
      var_count:   0,
      const_count: 0,
      hyps:        Vec::new(),
      asserts:     Vec::new(),

      stack: Vec::new(),
      disjoint_vars: HashSet::new(),
    })
  }

  fn apply(&mut self, assert: &Assertion) {
    // check to ensure that there are enough statements on the stack to apply assert
    if self.stack.len() < assert.hyps.len() {
      panic!("invalid");
    }

    // construct variable map and check that the stack matches assert's
    // hypotheses
    let mut var_map: HashMap<u32, Vec<Symbol>> = HashMap::new();
    let hyp_start = self.stack.len() - assert.hyps.len();
    for i in 0..assert.hyps.len() {
      let stack_entry = &self.stack[hyp_start + i];
      match &assert.hyps[i] {
        Hypothesis::F {t, var} => {
          if stack_entry.t != *t {
            panic!("invalid");
          }
          var_map.insert(*var, stack_entry.syms.clone());
        },
        Hypothesis::E (ss)     => {
          if stack_entry.t != ss.t {
            panic!("invalid");
          }

          let mut ss_sub = Vec::<Symbol>::new();
          for sym in &ss.syms {
            if sym.t == SymbolType::Var {
              let sub = var_map.get(&sym.id).unwrap();
              ss_sub.extend_from_slice(sub.as_slice());
            } else {
              ss_sub.push(sym.clone());
            }
          }

          if ss_sub.len() != stack_entry.syms.len() {
            panic!("invalid");
          }
          for i in 0..ss_sub.len() {
            if ss_sub[i] != stack_entry.syms[i] {
              panic!("invalid");
            }
          }
        },
      }
    }

    // Check the disjointness
    // first, construct map of variables to variables used in substitutions
    let mut var_var_map = HashMap::<u32, Vec<u32>>::new();
    let mut var_set = HashSet::<u32>::new();
    for (v, ss) in var_map.iter() {
      for s in ss {
        if s.t == SymbolType::Var {
          var_set.insert(s.id);
        }
      }
      let mut vars = Vec::<u32>::new();
      for v0 in var_set.drain() {
        vars.push(v0);
      }
      var_var_map.insert(*v, vars);
    }

    // Then, for every set of variables that must be disjoint, check that
    // their substitutions are disjoint.
    for (a, b) in assert.disjoint_vars.iter() {
      for s0 in var_var_map.get(a).unwrap() {
        for s1 in var_var_map.get(b).unwrap() {
          if s0 < s1 {
            if !self.disjoint_vars.contains(&(*s0, *s1)) {
              panic!("invalid");
            }
          } else {
            if !self.disjoint_vars.contains(&(*s1, *s0)) {
              panic!("invalid");
            }
          }
        }
      }
    }

    // The application is valid, drop the hypotheses from stack
    self.stack.truncate(hyp_start);

    // then push the substituted consequent to the stack.
    let mut consequent = SymStr { t: assert.consequent.t, syms: Vec::new() };
    for sym in &assert.consequent.syms {
      if sym.t == SymbolType::Var {
        consequent.syms.extend_from_slice(var_map.get(&sym.id).unwrap().as_slice());
      } else {
        consequent.syms.push(sym.clone());
      }
    }
    self.stack.push(consequent);
  }

  fn consume_symbol(&mut self, v: &mut Vec<u8>) {
    loop {
      let c = self.r.next();
      match c {
        TOK_WSP => return,
        0x21u8..=0x23u8 | 0x25u8..=0x7eu8 => v.push(c),
        _ => panic!("invalid"),
      }
    }
  }

  fn consume_label(&mut self, v: &mut Vec<u8>) {
    loop {
      let c = self.r.next();
      match c {
        TOK_WSP => return,
        ASCII_0..=ASCII_9 | ASCII_a..=ASCII_z | ASCII_A..=ASCII_Z | ASCII_DOT | ASCII_DASH | ASCII_UND => v.push(c),
        _ => panic!("invalid"),
      }
    }
  }

  fn get_typecode(&mut self) -> u32 {
    let mut symbol = Vec::<u8>::with_capacity(256);
    loop {
      let c = self.r.next();
      match c {
        TOK_WSP => continue,
        0x21u8..=0x23u8 | 0x25u8..=0x7eu8 => {
          symbol.push(c);
          self.consume_symbol(&mut symbol);
          let sym = self.sym_map.get(&symbol).unwrap();
          if sym.t != SymbolType::Const {
            panic!("invalid");
          }
          return sym.id;
        },
        _ => panic!("invalid"),
      }
    }
  }

  fn get_variable(&mut self) -> u32 {
    let mut symbol = Vec::<u8>::with_capacity(256);
    loop {
      match self.r.next() {
        TOK_EOF => panic!("EOF"),
        TOK_WSP => continue,
        // TODO: fix
        c       => {
          symbol.push(c);
          self.consume_symbol(&mut symbol);

          let sym = self.sym_map.get(&symbol).unwrap();
          if sym.t != SymbolType::Var {
            panic!("invalid");
          }
          return sym.id;
        },
      }
    }
  }

  fn consume_tok_dot(&mut self) {
    loop {
      match self.r.next() {
        TOK_WSP => continue,
        TOK_DOT => return,
        _ => panic!("invalid"),
      }
    }
  }

  fn parse_floating(&mut self) -> u32 {
    let t = self.get_typecode();
    let var = self.get_variable();
    self.consume_tok_dot();
    let id = self.hyps.len();
    self.hyps.push(Hypothesis::F{ t, var });
    return id as u32;
  }

  fn get_symbol_str(&mut self) -> Vec<Symbol> {
    let mut sym_str = Vec::<Symbol>::new();
    let mut sym_name = Vec::<u8>::new();
    loop {
      match self.r.next() {
        // TODO: fix
        TOK_EOF => panic!("EOF"),
        TOK_WSP => {
          if sym_name.len() > 0 {
            sym_str.push(self.sym_map.get(&sym_name).unwrap().clone());
            sym_name.clear();
          }
        },
        TOK_DOT => return sym_str,
        c       => sym_name.push(c),
      }
    }
  }

  fn parse_essential(&mut self) -> u32 {
    let t = self.get_typecode();
    let syms = self.get_symbol_str();
    let id = self.hyps.len();
    self.hyps.push(Hypothesis::E(SymStr { t, syms }));
    return id as u32;
  }

  fn create_assert(&mut self, sym_str: SymStr) -> u32 {
    let mut vars = HashSet::<u32>::new();
    for sym in &sym_str.syms {
      if sym.t == SymbolType::Var {
        vars.insert(sym.id);
      }
    }

    let mut hyps = Vec::<Hypothesis>::new();
    for h in &self.hyps {
      match h {
        Hypothesis::F { t:_ , var } =>
          if vars.contains(var) {
            hyps.push(h.clone());
          },
        Hypothesis::E(_) => hyps.push(h.clone()),
      }
    }

    let mut disjoint_vars = HashSet::<(u32, u32)>::new();
    for (a, b) in &self.disjoint_vars {
      if vars.contains(a) && vars.contains(b) {
        disjoint_vars.insert((*a, *b));
      }
    }

    let assert_id = self.asserts.len();
    self.asserts.push(Assertion {
      hyps: hyps,
      consequent: sym_str,
      disjoint_vars: disjoint_vars,
    });

    return assert_id as u32;
  }

  fn parse_axiom(&mut self) -> u32 {
    let t = self.get_typecode();
    let syms = self.get_symbol_str();
    return self.create_assert(SymStr { t: t, syms: syms });
  }

  fn parse_compressed_proof(&mut self) {
    /* labels */
    let mut symbol = Vec::<u8>::with_capacity(256);
    loop {
      match self.r.next() {
        // TODO: fix
        TOK_EOF  => panic!("EOF"),
        TOK_WSP => continue,
        ASCII_RPAR => break,
        c        => {
          symbol.push(c);
          loop {
            match self.r.next() {
              // TODO : fix
              TOK_EOF  => panic!("EOF"),
              TOK_WSP => break,
              c => symbol.push(c),
            }
          }
          /* TODO: symbol is symbol */
          symbol.clear();
        },
      }
    }
    /* compressed part */
    loop {
      match self.r.next() {
        TOK_EOF  => panic!("EOF"),
        TOK_WSP => continue,
        TOK_DOT => return,
        c        => {
          /* TODO */
        },
      }
    }
  }

  fn parse_proof(&mut self) -> u32 {
    self.get_typecode();

    /* get proof symbol str */
    let mut symbol = Vec::<u8>::with_capacity(256);
    loop {
      match self.r.next() {
        // TODO: fix
        TOK_EOF => panic!("EOF"),
        TOK_WSP => continue,
        TOK_EQ => break,
        c       => {
          symbol.push(c);
          self.consume_symbol(&mut symbol);
          /* TODO */
          symbol.clear();
        },
      }
    }

    /* get proof */
    loop {
      match self.r.next() {
        // TODO: fix
        TOK_EOF  => panic!("EOF"),
        TOK_WSP => continue,
        ASCII_LPAR => {
          self.parse_compressed_proof();
          panic!("TODO");
        },
        c        => {
          /* normal proof */
          symbol.push(c);
          self.consume_symbol(&mut symbol);
          /* TODO */
          symbol.clear();
          loop {
            let c = self.r.next();
            match c {
              TOK_WSP => {
                if symbol.len() > 0 {
                  // TODO
                  symbol.clear();
                }
              },
              TOK_DOT => {
                if self.stack.len() != 1 {
                  panic!("invalid");
                }
                // TODO: check that top of stack is same as assertion, then create assertion
                panic!("unimplemented");
              },
              ASCII_0..=ASCII_9 | ASCII_a..=ASCII_z | ASCII_A..=ASCII_Z | ASCII_DOT | ASCII_DASH | ASCII_UND => symbol.push(c),
              _       => panic!("invalid"),

            }
          }
        },
      }
    }
  }

  fn parse_constant_decl(&mut self) {
    let mut symbol = Vec::<u8>::new();
    loop {
      let c = self.r.next();
      match c {
        0x21u8..=0x23u8 | 0x25u8..=0x7eu8 => symbol.push(c),
        TOK_WSP => {
          if symbol.len() != 0 {
            let id = self.const_count;
            if self.sym_map.insert(symbol.clone(), Symbol { t: SymbolType::Const, id: id }).is_some() {
              panic!("invalid");
            }
            self.const_count += 1;
            symbol.clear();
          }
        },
        TOK_DOT => return,
        _ => panic!("invalid"),
      }
    }
  }

  fn parse_variable_decl(&mut self) {
    let mut symbol = Vec::<u8>::new();
    loop {
      let c = self.r.next();
      match c {
        0x21u8..=0x23u8 | 0x25u8..=0x7eu8 => symbol.push(c),
        TOK_WSP => {
          if symbol.len() != 0 {
            let id = self.var_count;
            if self.sym_map.insert(symbol.clone(), Symbol { t: SymbolType::Var, id: id }).is_some() {
              panic!("invalid");
            }
            self.var_count += 1;
            symbol.clear();
            
          }
        },
        TOK_DOT => return,
        _ => panic!("invalid"),
      }
    }
  }

  /*
   * If two variables replaced by a substitution exist in a mandatory $d
   * statement of the assertion referenced, the two expressions resulting from the
   * substitution must satisfy the following conditions.
   * 1) The two expressions must have no variables in common.
   * 2) Each possible pair of variables, one from each expression, must exist in
   *    an active $d statement of the $p statement containing the proof.
   */
  fn parse_disjoint_decl(&mut self) {
    let mut symbol = Vec::<u8>::new();
    let mut symbols = Vec::<u32>::new();
    loop {
      let c = self.r.next();
      match c {
        0x21u8..=0x23u8 | 0x25u8..=0x7eu8 => symbol.push(c),
        TOK_WSP => {
          if symbol.len() > 0 {
            let sym = self.sym_map.get(&symbol).unwrap();
            if sym.t != SymbolType::Var {
              panic!("invalid");
            }
            symbols.push(sym.id);
            symbol.clear();
          }
        },
        TOK_DOT => break,
        _ => panic!("invalid"),
      }
    }
    println!("symbols.len() = {}", symbols.len());
    if symbols.len() > 1 {
      for i in 0..symbols.len()-1 {
        for j in i..symbols.len() {
          /* TODO: symbols[i] symbols[j] are disjoint */
          let sym_i = symbols[i];
          let sym_j = symbols[j];
          // TODO: is this correct?
          // if sym_i == sym_j {
          //   panic!("invalid");
          // }
          if sym_i < sym_j {
            self.disjoint_vars.insert((sym_i, sym_j));
          } else {
            self.disjoint_vars.insert((sym_j, sym_i));
          }
        }
      }
    }
  }


  fn parse(&mut self) {

    let mut label = Vec::<u8>::with_capacity(256);
    let mut next_sym_id: u64 = 0;

    let mut block_symbols = Vec::<u32>::new();
    let mut block_sizes = Vec::<usize>::new();

    /* outer statements */
    loop {
      match self.r.next() {
        TOK_EOF => break,
        TOK_WSP => continue,
        TOK_CONST => {
          // TODO: check block 
          self.parse_constant_decl();
        },
        TOK_BLOCK_START => {
          block_sizes.push(block_symbols.len());
        },
        TOK_BLOCK_END  => {
          match block_sizes.pop() {
            Some(len) => {
              /* TODO */
              block_symbols.truncate(len);
            },
            None => panic!("invalid"),
          }
        },
        TOK_VAR => self.parse_variable_decl(),
        TOK_DISJOINT => self.parse_disjoint_decl(),
        // TODO: fix
        c        => {
          /* hypothesis or assert label*/
          label.push(c);
          self.consume_label(&mut label);

          // check for symbol reuse
          if let Some(v) = self.sym_map.get(&label) {
            panic!("symbol reuse");
          }

          /* hypothesis or assert statement */
          loop {
            match self.r.next() {
              TOK_WSP => continue,
              TOK_FLOATING => {
                let id = self.parse_floating();
                self.sym_map.insert(label.clone(), Symbol { t: SymbolType::Hyp, id: id });
              },
              TOK_ESSENTIAL => {
                let id = self.parse_essential();
                self.sym_map.insert(label.clone(), Symbol { t: SymbolType::Hyp, id: id });
              },
              TOK_AXIOM => {
                let id = self.parse_axiom();
                self.sym_map.insert(label.clone(), Symbol { t: SymbolType::Assert, id: id });
              },
              TOK_PROOF => {
                let id = self.parse_proof();
                self.sym_map.insert(label.clone(), Symbol { t: SymbolType::Assert, id: id });
              },
              _      => panic!("invalid"),
            }
          }

          label.clear();
        },
      }
    }
  }
}



fn main() {
  let args: Vec<String> = env::args().collect();
  if args.len() != 2 {
    return;
  }
  let fname = &args[1];
  let mut parser = Parser::new(fname).unwrap();
  parser.parse();
  println!("success!");
}
