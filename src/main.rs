#![allow(nonstandard_style)]
use std::collections::{ HashMap, HashSet, };
use std::env;
use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;

use num::{ BigUint, Zero, One };

/* -------------- tokens --------------- */
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
const ASCII_DOL: u8 = 0x24;
const ASCII_LPAR : u8 = 0x28;
const ASCII_RPAR : u8 = 0x29;
const ASCII_DASH : u8 = 0x2d;
const ASCII_DOT  : u8 = 0x2e;
const ASCII_0    : u8 = 0x30;
const ASCII_9    : u8 = 0x39;
const ASCII_EQ   : u8 = 0x3d;
const ASCII_QUESTION_MARK: u8 = 0x3f;
const ASCII_A    : u8 = 0x41;
const ASCII_T    : u8 = 0x54;
const ASCII_U    : u8 = 0x55;
const ASCII_Y    : u8 = 0x59;
const ASCII_Z    : u8 = 0x5a;
const ASCII_LSBR : u8 = 0x5b;
// const ASCII_RSBR : u8 = 0x5d;
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
            let buf = self.r.fill_buf().unwrap();
            if buf.is_empty() {
              panic!("invalid");
            } else {
              let v = buf[0];
              self.r.consume(1);
              // print!("<${}>", v as char);
              // std::io::stdout().flush();
              match v {
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
                ASCII_LSBR => panic!("unimplemented"),
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
          ASCII_TAB|ASCII_LF|ASCII_FF|ASCII_CR|ASCII_SP => {
            // print!("{}", ret as char);
            // std::io::stdout().flush();
            return TOK_WSP;
          },
          _ => {
            // print!("{}", ret as char);
            // std::io::stdout().flush();
            return ret;
          },
        }
      } else {
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

impl SymStr {
  fn new(t: u32) -> SymStr {
    return SymStr {
      t: t,
      syms: Vec::new(),
    };
  }
}

#[derive(Clone)]
enum Hypothesis {
  F { t: u32, var: u32 },
  E(SymStr),
}

impl Hypothesis {
  fn to_ss(&self) -> SymStr {
    match self {
      Hypothesis::F { t, var } =>
        SymStr {
          t: *t,
          syms: vec![
            Symbol { t: SymbolType::Var, id: *var }
          ]
        },
      Hypothesis::E(ss) => ss.clone(),
    }
  }
}

// Proof
// a proof is a series of steps.
// each step is either saved or not.
// steps can reference a hypothesis, a dependency, or a saved step
// 
enum ProofStep {
  Hyp(u32),
  Dep(u32),
  SaveDep(u32), // dependency + save to saved stack
  Saved(u32),
}

struct Assertion {
  name: String,
  is_axiom: bool,

  // The assertions that the proof of this assertion depends on.
  hyps: Vec<Hypothesis>,
  disjoint_vars: Vec<(u32, u32)>,
  consequent: SymStr,

  depends: Vec<Symbol>,
  opt_disjoint_vars: Vec<(u32, u32)>, // needed for proof
  proof: Vec<ProofStep>,
  // the total number of steps required to prove the statement
  // including the number of steps taken in all used theorems.
  // proof_steps: BigUint,

  // max_stack_size: u64,
}

struct Var {
  name: String,
}

struct Const {
  name: String,
}

struct Parser {
  r: TokReader,

  // symbols and data
  scope_local_names: HashSet<Vec<u8>>,
  sym_map:       HashMap<Vec<u8>, Symbol>,
  vars: Vec<Var>,
  consts: Vec<Const>,
  hyps: Vec<Hypothesis>,
  in_scope_hyps: Vec<u32>,
  disjoint_vars: HashSet<(u32, u32)>,

  asserts: Vec<Assertion>,
}

impl Parser {
  fn new(fname: &String) -> std::io::Result<Parser> {
    let f = File::open(fname)?;
    let r = TokReader::new(f);
    Ok(Parser {
      r: r,

      scope_local_names: HashSet::new(),
      sym_map:     HashMap::new(),
      vars:        Vec::new(),
      consts:      Vec::new(),
      hyps:        Vec::new(),
      in_scope_hyps: Vec::new(),
      disjoint_vars: HashSet::new(),

      asserts:     Vec::new(),
    })
  }

  fn apply(stack: &mut Vec<SymStr>, assert: &Assertion, disjoint_vars: &HashSet<(u32, u32)>) {
    // let assert = &self.asserts[assert_id as usize];
    // check to ensure that there are enough statements on the stack to apply assert
    if stack.len() < assert.hyps.len() {
      panic!("invalid");
    }

    // construct variable map and check that the stack matches assert's
    // hypotheses
    let mut var_map: HashMap<u32, Vec<Symbol>> = HashMap::new();
    let hyp_start = stack.len() - assert.hyps.len();
    for i in 0..assert.hyps.len() {
      let stack_entry = &stack[hyp_start + i];
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
    // println!("<<<disjoint_vars:");
    for (a, b) in &assert.disjoint_vars {
      // println!("\t$( ({}, {}) $)", a, b);
      for s0 in var_var_map.get(a).unwrap() {
        for s1 in var_var_map.get(b).unwrap() {
          if s0 < s1 {
            if !disjoint_vars.contains(&(*s0, *s1)) {
              panic!("invalid");
            }
          } else {
            if !disjoint_vars.contains(&(*s1, *s0)) {
              panic!("invalid");
            }
          }
        }
      }
    }
    // println!(">>>");

    // The application is valid, drop the hypotheses from stack
    stack.truncate(hyp_start);

    // then push the substituted consequent to the stack.
    let mut consequent = SymStr { t: assert.consequent.t, syms: Vec::new() };
    for sym in &assert.consequent.syms {
      if sym.t == SymbolType::Var {
        consequent.syms.extend_from_slice(var_map.get(&sym.id).unwrap().as_slice());
      } else {
        consequent.syms.push(sym.clone());
      }
    }
    stack.push(consequent);
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
        0x21u8..=0x23u8 | 0x25u8..=0x7eu8 => { /* printable ASCII minus '$' */
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
    let mut symbol = Vec::<u8>::new();
    loop {
      let tok = self.r.next();
      match tok {
        TOK_WSP => continue,
        0x21u8..=0x23u8 | 0x25u8..=0x7eu8 => { /* printable ASCII minus '$' */
          symbol.push(tok);
          self.consume_symbol(&mut symbol);

          let sym = self.sym_map.get(&symbol).unwrap();
          if sym.t != SymbolType::Var {
            panic!("invalid");
          }
          return sym.id;
        },
        _ => panic!("invalid"),
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
    self.in_scope_hyps.push(id as u32);
    return id as u32;
  }

  fn get_symbol_str(&mut self) -> Vec<Symbol> {
    let mut sym_str = Vec::<Symbol>::new();
    let mut sym_name = Vec::<u8>::new();
    loop {
      let tok = self.r.next();
      match tok {
        TOK_WSP => {
          if sym_name.len() > 0 {
            sym_str.push(self.sym_map.get(&sym_name).unwrap().clone());
            sym_name.clear();
          }
        },
        TOK_DOT => return sym_str,
        /* printable ASCII minus '$' */
        0x21u8..=0x23u8 | 0x25u8..=0x7eu8 => sym_name.push(tok),
        _ => panic!("invalid"),
      }
    }
  }

  fn parse_essential(&mut self) -> u32 {
    let t = self.get_typecode();
    let syms = self.get_symbol_str();
    let id = self.hyps.len();
    self.hyps.push(Hypothesis::E(SymStr { t, syms }));
    self.in_scope_hyps.push(id as u32);
    return id as u32;
  }

  fn get_mandatory_vars(&self, sym_str: &SymStr) -> HashSet<u32> {
    let mut vars = HashSet::<u32>::new();
    for sym in &sym_str.syms {
      if sym.t == SymbolType::Var {
        vars.insert(sym.id);
      }
    }
    for id in self.in_scope_hyps.iter() {
      let h = &self.hyps[*id as usize];
      if let Hypothesis::E(ss) = h {
        for sym in &ss.syms {
          if sym.t == SymbolType::Var {
            vars.insert(sym.id);
          }
        }
      }
    }

    return vars;
  }
  fn get_mandatory_hyps(&self, mand_vars: &HashSet<u32>) -> Vec<Hypothesis> {
    let mut hyps = Vec::<Hypothesis>::new();
    for id in self.in_scope_hyps.iter() {
      let h = &self.hyps[*id as usize];
      match h {
        Hypothesis::F { t:_ , var } =>
          if mand_vars.contains(var) {
            hyps.push(h.clone());
          },
        Hypothesis::E(_) => hyps.push(h.clone()),
      }
    }
    return hyps;
  }

  fn get_disjoint_vars(&self, mand_vars: &HashSet<u32>) -> Vec<(u32, u32)> {
    let mut disjoint_vars = Vec::<(u32, u32)>::new();
    for (a, b) in &self.disjoint_vars {
      if mand_vars.contains(a) && mand_vars.contains(b) {
        disjoint_vars.push((*a, *b));
      }
    }
    return disjoint_vars;
  }

  fn parse_axiom(&mut self, name: String) -> u32 {
    let t = self.get_typecode();
    let syms = self.get_symbol_str();
    let consequent = SymStr { t, syms };
    let vars = self.get_mandatory_vars(&consequent);
    let hyps = self.get_mandatory_hyps(&vars);
    let disjoint_vars = self.get_disjoint_vars(&vars);

    let assert_id = self.asserts.len();
    self.asserts.push(Assertion {
      name: name,
      is_axiom: true,
      hyps: hyps,
      consequent: consequent,
      disjoint_vars: disjoint_vars,
      depends: vec![],
      opt_disjoint_vars: vec![],
      proof: vec![],
    });

    return assert_id as u32;
  }

  fn is_valid_proof(&self, consequent: &SymStr, hyps: &Vec<Hypothesis>,
      disjoint_vars: &HashSet<(u32, u32)>, deps: &Vec<Symbol>, proof: &Vec<ProofStep>) -> bool {
    let mut stack = Vec::<SymStr>::new();
    let mut saved_statements = Vec::<SymStr>::new();

    // verify validity of every proof step
    // let mut step_count = 0;
    // println!("proving {}", self.render_ss(consequent));
    for step in proof {
      // println!("step {}:", step_count);
      // step_count += 1;
      // for ss in stack.iter() {
      //   println!("\t{}", self.render_ss(ss));
      // }
      match step {
        ProofStep::Hyp(id) => {
          // println!("h");
          let hyp = &hyps[*id as usize];
          stack.push(hyp.to_ss());
        },
        ProofStep::Dep(id) => {
          // println!("d");
          let sym = &deps[*id as usize];
          match sym.t {
            SymbolType::Hyp => {
              let hyp = &self.hyps[sym.id as usize];
              stack.push(hyp.to_ss());
            },
            SymbolType::Assert => {
              let assert = &self.asserts[sym.id as usize];
              Parser::apply(&mut stack, assert, disjoint_vars);
            },
            _ => unreachable!(),
          }
        },
        ProofStep::SaveDep(id) => {
          let sym = &deps[*id as usize];
          match sym.t {
            SymbolType::Hyp => {
              let hyp = &self.hyps[sym.id as usize];
              stack.push(hyp.to_ss());
            },
            SymbolType::Assert => {
              let assert = &self.asserts[sym.id as usize];
              Parser::apply(&mut stack, assert, disjoint_vars);
            },
            _ => unreachable!(),
          }
          saved_statements.push(stack[stack.len()-1].clone());
        },
        ProofStep::Saved(id) => {
          let st = saved_statements[*id as usize].clone();
          // println!("<saved statement {}>", self.render_ss(&st));
          stack.push(st);
          
        },
      }
    }

    // check that top of stack matches consequent
    if stack.len() != 1 {
      println!("stack.len(): {}", stack.len());
      panic!("invalid");
      return false;
    }
    // check that top of stack is same as assertion, then create assertion
    if consequent.syms.len() != stack[0].syms.len() {
      panic!("invalid");
      return false;
    }
    if consequent.t != stack[0].t {
      panic!("invalid");
      return false;
    }
    for i in 0..consequent.syms.len() {
      if consequent.syms[i] != stack[0].syms[i] {
        panic!("invalid");
        return false;
      }
    }
    return true;
  }

  fn parse_compressed_proof(&mut self, name: String, consequent: SymStr) -> u32 {
    let mand_vars = self.get_mandatory_vars(&consequent);
    let mut opt_vars = HashSet::<u32>::new();
    let hyps = self.get_mandatory_hyps(&mand_vars);

    println!("$( verifying {}:", name);
    for (a, b) in self.disjoint_vars.iter() {
      println!("\t$d {} {} $.", self.vars[*a as usize].name, self.vars[*b as usize].name);
    }

    /* get labels */
    let mut sym_name = Vec::<u8>::new();
    let mut labels = Vec::<Symbol>::new();
    loop {
      let tok = self.r.next();
      match tok {
        TOK_WSP => {
          if sym_name.len() > 0 {
            let sym = self.sym_map.get(&sym_name).unwrap();
            // println!("sym_name: {} (id: {})", String::from_utf8(sym_name.clone()).unwrap(), sym.id);
            sym_name.clear();
            if sym.t != SymbolType::Hyp && sym.t != SymbolType::Assert {
              panic!("invalid");
            }
            if sym.t == SymbolType::Hyp {
              // println!("\t{}", self.render_hyp(&self.hyps[sym.id as usize]));
              if let Hypothesis::F { t , var } = self.hyps[sym.id as usize] {
                opt_vars.insert(var);
              }
            }
            labels.push(sym.clone());
          }          
        },
        ASCII_RPAR => {
          /* end labels */
          if sym_name.len() != 0 {
            panic!("invalid");
          }
          break;
        },
        ASCII_0..=ASCII_9 | ASCII_a..=ASCII_z | ASCII_A..=ASCII_Z | ASCII_DOT | ASCII_DASH | ASCII_UND => sym_name.push(tok),
        _ => panic!("invalid"),
      }
    }

    print!("mand vars:");
    for var in mand_vars.iter() {
      print!(" {}", self.vars[*var as usize].name);
    }
    println!("");

    print!("opt vars:");
    for var in opt_vars.iter() {
      print!(" {}", self.vars[*var as usize].name);
    }
    println!("");

    // construct proof
    let mut proof = Vec::<ProofStep>::new();
    let mut saved_statement_count = 0;
    let mut num: usize = 0;
    loop {
      let tok = self.r.next();
      match tok {
        TOK_WSP => continue,
        TOK_DOT => break,
        ASCII_A..=ASCII_T => {
          num = 20 * num;
          num += (tok - ASCII_A) as usize;
          // print!(" {}", num);

          // mandatory hypothesis
          if num < hyps.len() {
            proof.push(ProofStep::Hyp(num as u32));

            num = 0;
            continue;
          }

          // label
          num -= hyps.len();
          if num < labels.len() {
            proof.push(ProofStep::Dep(num as u32));

            num = 0;
            continue;
          }

          // saved statement
          num -= labels.len();
          if num < saved_statement_count {
            proof.push(ProofStep::Saved(num as u32));

            num = 0;
            continue;
          }

          // number too large
          panic!("invalid");
        },
        ASCII_U..=ASCII_Y => {
          num = 5 * num;
          num = num + (tok - ASCII_U + 1) as usize;
        },
        ASCII_Z => {
          if proof.len() == 0 {
            panic!("invalid");
          }
          match proof.pop().unwrap() {
            ProofStep::Dep(id) => proof.push(ProofStep::SaveDep(id)),
            _ => panic!("invalid"),
          } 
          saved_statement_count += 1;
        },
        _ => panic!("invalid"),
      }
    }

    println!("\n$)");

    let disjoint_vars = self.get_disjoint_vars(&mand_vars);
    if self.is_valid_proof(&consequent, &hyps, &self.disjoint_vars, &labels, &proof) {
      let mut opt_disjoint_vars = Vec::<(u32, u32)>::new();
      // let mut all_vars = mand_vars.clone();
      // all_vars.union(&opt_vars);
      print!("$( opt disjoint vars:");
      // print!("all vars:");
      // for var in all_vars.iter() {
      //   print!(" {}", self.vars[*var as usize].name);
      // }
      // println!("");
      for a in mand_vars.union(&opt_vars) {
        for b in opt_vars.iter() {
          println!("checking {}({}) {}({})",
            self.vars[*a as usize].name, *a,
            self.vars[*b as usize].name, *b);
          if a <= b {
            let pair = (*a, *b);
            if self.disjoint_vars.get(&pair).is_some() {
              opt_disjoint_vars.push(pair);
            }
          } else {
            let pair = (*b, *a);
            if self.disjoint_vars.get(&pair).is_some() {
              opt_disjoint_vars.push(pair);
            }
          }
        }
      }

      for (a, b) in opt_disjoint_vars.iter() {
        print!(" ({}, {})",
          self.vars[*a as usize].name,
          self.vars[*b as usize].name,
        );
      }
      println!("opt_disjoint_vars.len() {} disjoint_vars.len() {}",
        opt_disjoint_vars.len(), disjoint_vars.len()
      );
      println!(" $)");

      let assert_id = self.asserts.len();
      self.asserts.push(Assertion {
        name: name,
        is_axiom: false,
        hyps: hyps,
        consequent: consequent,
        disjoint_vars: disjoint_vars,
        opt_disjoint_vars: opt_disjoint_vars,

        depends: labels,
        proof: proof,
      });

      return assert_id as u32;
    } else {
      panic!("invalid");
    }



  }

  fn parse_proof(&mut self, name: String) -> u32 {
    // cleanup stack from potential previous iteration
    let t = self.get_typecode();

    /* get proof symbol str */
    let mut consequent = SymStr::new(t);
    let mut sym_name = Vec::<u8>::new();
    loop {
      let tok = self.r.next();
      match tok {
        TOK_WSP => {
          if sym_name.len() > 0 {
            consequent.syms.push(self.sym_map.get(&sym_name).unwrap().clone());
            sym_name.clear();
          }
        },
        TOK_EQ => {
          if sym_name.len() != 0 {
            panic!("invalid");
          }
          break;
        },
        /* printable ASCII minus '$' */
        0x21u8..=0x23u8 | 0x25u8..=0x7eu8 => sym_name.push(tok),
        _ => panic!("invalid"),
      }
    }

    /* normal or compressed proof? */
    loop {
      let tok = self.r.next();
      match tok {
        TOK_WSP => continue,
        ASCII_LPAR => {
          /* compressed proof */
          return self.parse_compressed_proof(name, consequent);
        },
        ASCII_0..=ASCII_9 | ASCII_a..=ASCII_z | ASCII_A..=ASCII_Z | ASCII_DOT
        | ASCII_DASH | ASCII_UND => {
          /* normal proof */
          sym_name.push(tok);
          break;

        },
        ASCII_QUESTION_MARK => {
          panic!("unimplemented");
          // TODO: need to consume to end of proof
          /* assume valid */
          // return self.create_assert(name, sym_str);
        },
        _ => panic!("invalid"),
      }
    }

    /* process normal proof */
    let mut proof_steps = BigUint::zero();
    let mut stack = Vec::<SymStr>::new();
    loop {
      let tok = self.r.next();
      match tok {
        TOK_WSP => {
          if sym_name.len() == 0 {
            continue;
          }

          /* process symbol */
          let sym = self.sym_map.get(&sym_name).unwrap();
          sym_name.clear();

          match sym.t {
            SymbolType::Hyp => {
              let hyp = &self.hyps[sym.id as usize];
              stack.push(hyp.to_ss());
              proof_steps += 1u32;
            },
            SymbolType::Assert => {
              let assert = &self.asserts[sym.id as usize];
              Parser::apply(&mut stack, assert, &self.disjoint_vars);
            },
            _ => panic!("invalid"),
          }
        },
        ASCII_0..=ASCII_9 | ASCII_a..=ASCII_z | ASCII_A..=ASCII_Z | ASCII_DOT | ASCII_DASH | ASCII_UND => sym_name.push(tok),
        TOK_DOT => {
          /* end of proof */
          if stack.len() != 1 {
            panic!("invalid");
          }
          // check that top of stack is same as assertion, then create assertion
          if consequent.syms.len() != stack[0].syms.len() {
            panic!("invalid");
          }
          if consequent.t != stack[0].t {
            panic!("invalid");
          }
          for i in 0..consequent.syms.len() {
            if consequent.syms[i] != stack[0].syms[i] {
              panic!("invalid");
            }
          }
          panic!("TODO: broken");
          // return self.create_assert(name, false, consequent);
        },
        ASCII_QUESTION_MARK => {
          // TODO: need to read to end of proof first.
          panic!("unimplemented");
          // return self.create_assert(sym_str);
        },
        _ => panic!("invalid"),
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
            let id = self.consts.len() as u32;
            if self.sym_map.insert(symbol.clone(), Symbol { t: SymbolType::Const, id: id }).is_some() {
              panic!("invalid");
            }
            self.consts.push(Const { name: String::from_utf8(symbol.clone()).unwrap() });
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
          if symbol.len() > 0 {
            let id = self.vars.len() as u32;
            if let Some(sym) = self.sym_map.get(&symbol) {
              match sym.t {
                SymbolType::Var => {},
                _ => panic!("invalid"),
              }
            } else {
              self.sym_map.insert(symbol.clone(), Symbol { t: SymbolType::Var, id: id });
              self.vars.push(Var { name: String::from_utf8(symbol.clone()).unwrap() });
            }
            // self.scope_local_names.insert(symbol.clone());
            symbol.clear();
          }
        },
        TOK_DOT => {
          if symbol.len() != 0 {
            panic!("invalid");
          }
          return;
        },
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
            // println!("<sym.id {} symbol {}>", sym.id, String::from_utf8(symbol.clone()).unwrap());
            symbols.push(sym.id);
            symbol.clear();
          }
        },
        TOK_DOT => break,
        _ => panic!("invalid"),
      }
    }
    // println!("symbols.len() = {}", symbols.len());
    // println!("<symbols {:?}>", symbols);
    if symbols.len() > 1 {
      for i in 0..symbols.len()-1 {
        for j in i+1..symbols.len() {
          /* TODO: symbols[i] symbols[j] are disjoint */
          let sym_i = symbols[i];
          let sym_j = symbols[j];
          // println!("<sym_i {} sym_j {}>", sym_i, sym_j);
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

    let mut scope_local_names_stack = Vec::<HashSet<Vec<u8>>>::new();
    let mut hyps_len_stack = Vec::<usize>::new();
    let mut disjoint_vars_stack = Vec::<HashSet<(u32, u32)>>::new();

    /* outer statements */
    loop {
      let tok = self.r.next();
      match tok {
        TOK_EOF => break,
        TOK_WSP => continue,
        TOK_CONST => {
          // TODO: check block 
          if hyps_len_stack.len() > 0 {
            panic!("invalid");
          }
          self.parse_constant_decl();
        },
        TOK_BLOCK_START => {
          scope_local_names_stack.push(self.scope_local_names.clone());
          self.scope_local_names = HashSet::new();
          hyps_len_stack.push(self.in_scope_hyps.len());
          disjoint_vars_stack.push(self.disjoint_vars.clone());
        },
        TOK_BLOCK_END  => {
          for name in &self.scope_local_names {
            self.sym_map.remove(name);
          }
          self.scope_local_names = scope_local_names_stack.pop().unwrap();
          self.in_scope_hyps.truncate(hyps_len_stack.pop().unwrap());
          self.disjoint_vars = disjoint_vars_stack.pop().unwrap();
          // for (name, _) in self.sym_map
          // print!("{}", ret as char);
          // std::io::stdout().flush();
        },
        TOK_VAR => self.parse_variable_decl(),
        TOK_DISJOINT => self.parse_disjoint_decl(),
        // TODO: fix
        ASCII_0..=ASCII_9 | ASCII_a..=ASCII_z | ASCII_A..=ASCII_Z | ASCII_DOT
        | ASCII_DASH | ASCII_UND => {
          /* hypothesis or assert label*/
          label.push(tok);
          self.consume_label(&mut label);

          // check for symbol reuse
          if self.sym_map.get(&label).is_some() {
            panic!("symbol reuse");
          }

          /* hypothesis or assert statement */
          loop {
            match self.r.next() {
              TOK_WSP => continue,
              TOK_FLOATING => {
                self.scope_local_names.insert(label.clone());
                let id = self.parse_floating();
                self.sym_map.insert(label.clone(), Symbol { t: SymbolType::Hyp, id: id });
                break;
              },
              TOK_ESSENTIAL => {
                self.scope_local_names.insert(label.clone());
                let id = self.parse_essential();
                self.sym_map.insert(label.clone(), Symbol { t: SymbolType::Hyp, id: id });
                break;
              },
              TOK_AXIOM => {
                let label_name = String::from_utf8(label.clone()).unwrap();
                let id = self.parse_axiom(label_name);
                self.sym_map.insert(label.clone(), Symbol { t: SymbolType::Assert, id: id });
                break;
              },
              TOK_PROOF => {
                let label_name = String::from_utf8(label.clone()).unwrap();
                let id = self.parse_proof(label_name);
                self.sym_map.insert(label.clone(), Symbol { t: SymbolType::Assert, id: id });
                break;
              },
              _      => panic!("invalid"),
            }
          }

          label.clear();
        },
        _ => panic!("invalid"),
      }
    }
  }

  fn render_ss(&self, ss: &SymStr) -> String {
    let mut out = String::new();
    out.push_str(self.consts[ss.t as usize].name.as_str());
    for sym in ss.syms.iter() {
      let name = match sym.t {
        SymbolType::Const => {
          self.consts[sym.id as usize].name.as_str()
        },
        SymbolType::Var => {
          self.vars[sym.id as usize].name.as_str()
        },
        _ => panic!("invalid"),
      };
      out.push(' ');
      out.push_str(name);
    }
    return out;
  }

  fn display_asserts(&self) {
    for assert in &self.asserts {
      println!("----------------");
      println!("{}:", assert.name);
      // println!("\tproof steps: {}", assert.proof_steps);
      // println!("\tmax stack size: {}", assert.max_stack_size);
      for (i, hyp) in assert.hyps.iter().enumerate() {
        let ss = hyp.to_ss();
        println!("\th{}: {}", i, self.render_ss(&ss));
      }
      println!("\t{}", self.render_ss(&assert.consequent));
    }
  }

  fn render_hyp(&self, hyp: &Hypothesis) -> String {
    let mut out = String::new();
    match hyp {
      Hypothesis::F{ t, var } => {
        out.push_str(format!("$f {} {} $.",
          self.consts[*t as usize].name, self.vars[*var as usize].name).as_str());
      },
      Hypothesis::E(ss) => {
        out.push_str(format!("$e {} $.", self.render_ss(ss)).as_str());
      },
    }
    return out;
  }

  fn num_to_mm_enc(mut num: u32) -> String {
    let mut buf = Vec::<u8>::new();
    buf.push('A' as u8 + (num % 20) as u8);
    num = num / 20;
    while num != 0 {
      num -= 1;
      buf.push('U' as u8 + (num % 5) as u8);
      num /= 5;
    }
    buf.reverse();
    return String::from_utf8(buf).unwrap()
  }

  fn print_mm(&self) {
    println!("$( constants $)");
    for c in self.consts.iter() {
      println!("\t$c {} $.", c.name);
    }
    println!("$( variables $)");
    for v in self.vars.iter() {
      println!("\t$v {} $.", v.name);
    }
    for assert in self.asserts.iter() {
      println!("${{");
      // disjoints
      for (a, b) in assert.disjoint_vars.iter() {
        println!("\t$d {} {} $.", self.vars[*a as usize].name, self.vars[*b as usize].name);
      }
      for (a, b) in assert.opt_disjoint_vars.iter() {
        println!("\t$d {} {} $.", self.vars[*a as usize].name, self.vars[*b as usize].name);
      }

      println!("");

      // optional hypotheses
      println!("\t$( number of depends: {} $)", assert.depends.len());
      for (i, d) in assert.depends.iter().enumerate() {
        match d.t {
          SymbolType::Hyp => {
            println!("\t{}.opt{} {}", assert.name, i, self.render_hyp(&self.hyps[d.id as usize]));
          },
          _ => continue,
        }
      }

      println!("");

      // hypotheses
      for (i, hyp) in assert.hyps.iter().enumerate() {
        println!("\t{}.h{} {}", assert.name, i, self.render_hyp(hyp));
      }

      if assert.is_axiom {
        println!("\t{} $a {} $.", assert.name, self.render_ss(&assert.consequent));
      } else {
        println!("\t{} $p {} $=", assert.name, self.render_ss(&assert.consequent));

        // depends
        print!("\t(");
        for (i, d) in assert.depends.iter().enumerate() {
          match d.t {
            SymbolType::Hyp => {
              print!(" {}.opt{}", assert.name, i);
            },
            SymbolType::Assert => {
              print!(" {}", self.asserts[d.id as usize].name);
              
            },
            _ => panic!("invalid"),
          }
        }
        println!(" )");

        let hyps_len = assert.hyps.len() as u32;
        let deps_len = assert.depends.len() as u32;
        for step in assert.proof.iter() {
          match step {
            ProofStep::Hyp(id) => {
              print!("{}", Parser::num_to_mm_enc(*id));
            },
            ProofStep::Dep(id) => {
              print!("{}", Parser::num_to_mm_enc(*id + hyps_len));
            },
            ProofStep::SaveDep(id) => {
              print!("{}", Parser::num_to_mm_enc(*id + hyps_len));
              print!("Z");
            },
            ProofStep::Saved(id) => {
              print!("{}", Parser::num_to_mm_enc(*id + hyps_len + deps_len));
            },
          }
        }

        // proof
        println!(" $.");
      }
      println!("$}}");
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
  // parser.display_asserts();
  parser.print_mm();
  // println!("success!");
}
