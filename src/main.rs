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
  SaveDep(u32),
  Saved(u32),
  
}
struct Proof {
}

struct Assertion {
  name: String,
  // the total number of steps required to prove the statement
  // including the number of steps taken in all used theorems.
  axiom: bool,
  proof_steps: BigUint,
  // The assertions that the proof of this assertion depends on.
  depends: Vec<u32>,
  proof: Vec<ProofStep>,
  max_stack_size: u64,
  hyps: Vec<Hypothesis>,
  consequent: SymStr,
  disjoint_vars: Vec<(u32, u32)>,
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
  disjoint_vars: HashSet<(u32, u32)>,

  asserts: Vec<Assertion>,

  // proof state?
  stack:         Vec<SymStr>,
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
      disjoint_vars: HashSet::new(),

      asserts:     Vec::new(),

      stack: Vec::new(),
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
      // println!("\t({}, {})", a, b);
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
    return id as u32;
  }

  fn get_mandatory_vars(&self, sym_str: &SymStr) -> HashSet<u32> {
    let mut vars = HashSet::<u32>::new();
    for sym in &sym_str.syms {
      if sym.t == SymbolType::Var {
        vars.insert(sym.id);
      }
    }
    for h in &self.hyps {
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
    for h in &self.hyps {
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

  fn create_assert(&mut self, name: String, proof_steps: BigUint,
    max_stack_size: u64,
    sym_str: SymStr) -> u32 {
    // get vars in consequent and all essential hypotheses
    let vars = self.get_mandatory_vars(&sym_str);
    let hyps = self.get_mandatory_hyps(&vars);
    let disjoint_vars = self.get_disjoint_vars(&vars);

    let assert_id = self.asserts.len();
    self.asserts.push(Assertion {
      name: name,
      proof_steps: proof_steps,
      max_stack_size: max_stack_size,
      hyps: hyps,
      consequent: sym_str,
      disjoint_vars: disjoint_vars,
    });

    // println!(">>>");
    return assert_id as u32;
  }

  fn parse_axiom(&mut self, name: String) -> u32 {
    let t = self.get_typecode();
    let syms = self.get_symbol_str();
    return self.create_assert(name, BigUint::zero() + 1u32, 0, SymStr { t: t, syms: syms });
  }

  fn parse_compressed_proof(&mut self, name: String, sym_str: SymStr) -> u32 {
    let vars = self.get_mandatory_vars(&sym_str);
    let hyps = self.get_mandatory_hyps(&vars);

    /* get labels */
    let mut sym_name = Vec::<u8>::new();
    let mut labels = Vec::<&Symbol>::new();
    loop {
      let tok = self.r.next();
      match tok {
        TOK_WSP => {
          if sym_name.len() > 0 {
            let sym = self.sym_map.get(&sym_name).unwrap();
            sym_name.clear();
            if sym.t != SymbolType::Hyp && sym.t != SymbolType::Assert {
              panic!("invalid");
            }
            labels.push(sym);
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
    // println!("<--------------------------------------------------->");

    /* compressed part */
    let mut num: usize = 0;
    let mut proof_steps = BigUint::zero();
    let mut max_stack_size = 0;
    // TODO
    let mut saved_statements = Vec::<SymStr>::new();
    // track the number of steps taken to create a particular entry on the stack.
    // necessary for counting steps when repeating
    // this tracks the number of proof steps for each item on the stack
    let mut stack_steps = Vec::<BigUint>::new(); 
    // this tracks the number of proof steps for each saved item
    let mut saved_statement_steps = Vec::<BigUint>::new();
    loop {
      let tok = self.r.next();
      match tok {
        TOK_WSP => continue,
        TOK_DOT => {
          let disjoint_vars = self.get_disjoint_vars(&vars);

          let assert_id = self.asserts.len();
          self.asserts.push(Assertion {
            name: name,
            proof_steps: proof_steps,
            max_stack_size: max_stack_size,
            hyps: hyps,
            consequent: sym_str,
            disjoint_vars: disjoint_vars,
          });

          return assert_id as u32;
        },
        ASCII_A..=ASCII_T => {
          num = 20 * num;
          num += (tok - ASCII_A) as usize;

          // mandatory hypothesis
          if num < hyps.len() {
            let hyp = &hyps[num];
            self.stack.push(hyp.to_ss());

            stack_steps.push(BigUint::one());
            proof_steps += 1u32;

            num = 0;
            continue;
          }

          // label
          num -= hyps.len();
          if num < labels.len() {
            let sym = labels[num];
            match sym.t {
              SymbolType::Hyp => {
                let hyp = &self.hyps[sym.id as usize];
                self.stack.push(hyp.to_ss());

                stack_steps.push(BigUint::one());
                proof_steps += 1u32;
              },
              SymbolType::Assert => {
                let assert = &self.asserts[sym.id as usize];

                // calculate the number of steps taken to in this statement's
                // hypotheses
                let mut steps = BigUint::zero();
                if assert.hyps.len() > self.stack.len() {
                  panic!("invalid");
                }
                let stack_start = self.stack.len() - assert.hyps.len();
                for i in 0..assert.hyps.len() {
                  steps += &stack_steps[stack_start + i];
                }
                stack_steps.truncate(stack_start);
                stack_steps.push(assert.proof_steps.clone() + steps);

                Parser::apply(&mut self.stack, assert, &self.disjoint_vars);

                proof_steps += &assert.proof_steps;
              },
              _ => unreachable!(),
            }

            num = 0;
            continue;
          }

          // saved statement
          num -= labels.len();
          if num < saved_statements.len() {
            let st = saved_statements[num].clone();
            // println!("<saved statement {}>", self.render_ss(&st));
            self.stack.push(st);
            stack_steps.push(saved_statement_steps[num].clone());

            proof_steps += &saved_statement_steps[num];
            
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
          // Save statement from top of stack. Since we generated it once, we
          // know that it is possible to generate it again, so we don't have
          // to check the steps to create it a second time.
          if self.stack.len() == 0 {
            panic!("invalid");
          }
          // println!("<saving statement: {}>", self.render_ss(&self.stack[self.stack.len()-1]));
          saved_statements.push(self.stack[self.stack.len()-1].clone());
          saved_statement_steps.push(stack_steps[self.stack.len()-1].clone());
        },
        _ => panic!("invalid"),
      }
    }
  }

  fn parse_proof(&mut self, name: String) -> u32 {
    // cleanup stack from potential previous iteration
    self.stack.clear();

    let t = self.get_typecode();

    /* get proof symbol str */
    let mut sym_str = SymStr::new(t);
    let mut sym_name = Vec::<u8>::new();
    loop {
      let tok = self.r.next();
      match tok {
        TOK_WSP => {
          if sym_name.len() > 0 {
            sym_str.syms.push(self.sym_map.get(&sym_name).unwrap().clone());
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
          return self.parse_compressed_proof(name, sym_str);
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
              self.stack.push(hyp.to_ss());
              proof_steps += 1u32;
            },
            SymbolType::Assert => {
              let assert = &self.asserts[sym.id as usize];
              Parser::apply(&mut self.stack, assert, &self.disjoint_vars);
              proof_steps += &assert.proof_steps;
            },
            _ => panic!("invalid"),
          }
        },
        ASCII_0..=ASCII_9 | ASCII_a..=ASCII_z | ASCII_A..=ASCII_Z | ASCII_DOT | ASCII_DASH | ASCII_UND => sym_name.push(tok),
        TOK_DOT => {
          /* end of proof */
          if sym_name.len() != 0 {
            panic!("invalid");
          }
          if self.stack.len() != 1 {
            panic!("invalid");
          }
          // check that top of stack is same as assertion, then create assertion
          if sym_str.syms.len() != self.stack[0].syms.len() {
            panic!("invalid");
          }
          if sym_str.t != self.stack[0].t {
            panic!("invalid");
          }
          for i in 0..sym_str.syms.len() {
            if sym_str.syms[i] != self.stack[0].syms[i] {
              panic!("invalid");
            }
          }
          panic!("TODO: max stack size");
          return self.create_assert(name, proof_steps, 0, sym_str);
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
            if self.sym_map.insert(symbol.clone(), Symbol { t: SymbolType::Var, id: id }).is_some() {
              panic!("invalid");
            }
            self.scope_local_names.insert(symbol.clone());
            self.vars.push(Var { name: String::from_utf8(symbol.clone()).unwrap() });
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
          hyps_len_stack.push(self.hyps.len());
          disjoint_vars_stack.push(self.disjoint_vars.clone());
        },
        TOK_BLOCK_END  => {
          for name in &self.scope_local_names {
            self.sym_map.remove(name);
          }
          self.scope_local_names = scope_local_names_stack.pop().unwrap();
          self.hyps.truncate(hyps_len_stack.pop().unwrap());
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
      println!("\tproof steps: {}", assert.proof_steps);
      println!("\tmax stack size: {}", assert.max_stack_size);
      for (i, hyp) in assert.hyps.iter().enumerate() {
        let ss = hyp.to_ss();
        println!("\th{}: {}", i, self.render_ss(&ss));
      }
      println!("\t{}", self.render_ss(&assert.consequent));
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
  parser.display_asserts();
  println!("success!");
}
