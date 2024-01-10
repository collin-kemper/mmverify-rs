use std::collections::{ HashMap, HashSet, VecDeque };
use std::io::prelude::*;

use rand::prelude::*;

#[derive(PartialEq, Eq, Clone)]
pub enum SymbolType {
  Var,
  Const,
  Hyp,
  Assert,
}

#[derive(PartialEq, Eq, Clone)]
pub struct Symbol {
  pub t: SymbolType,
  pub id: u32,
}

#[derive(Clone)]
pub struct SymStr {
  pub t: u32,
  pub syms: Vec<Symbol>,
}

impl SymStr {
  pub fn new(t: u32) -> SymStr {
    return SymStr {
      t: t,
      syms: Vec::new(),
    };
  }
}

#[derive(Clone)]
pub struct VarDecl {
  pub t: u32,
  pub var: u32,
}

#[derive(Clone)]
pub enum Hypothesis {
  F(VarDecl),
  E(SymStr),
}

impl Hypothesis {
  fn to_ss(&self) -> SymStr {
    match self {
      Hypothesis::F(decl) =>
        SymStr {
          t: decl.t,
          syms: vec![
            Symbol { t: SymbolType::Var, id: decl.var }
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
#[derive(Clone)]
pub enum ProofStep {
  Hyp(u32),
  Dep(u32),
  Saved(u32),
}

// This is more thorough data about the mechanics of a proof step.
// struct StepData {
//   start_step: u32,
//   result: SymStr,
//   // what I did
// }

#[derive(Clone)]
struct Assertion {
  name: String,
  is_axiom: bool,

  // The assertions that the proof of this assertion depends on.
  hyps: Vec<Hypothesis>,
  disjoint_vars: Vec<(u32, u32)>,
  consequent: SymStr,

  deps: Vec<Symbol>,
  // opt_disjoint_vars: Vec<(u32, u32)>, // needed for proof
  proof: Vec<ProofStep>,
}

impl Assertion {
  fn get_mand_var_set(&self) -> HashSet<u32> {
    let mut mand_var_set = HashSet::<u32>::new();
    for hyp in self.hyps.iter() {
      match hyp {
        Hypothesis::F(decl) => { mand_var_set.insert(decl.var); },
        _ => {},
      }
    }
    return mand_var_set;
  }
}

struct Var {
  name: String,
  type_declared: bool,
  t: u32,
}

struct Const {
  name: String,
}

pub struct MmDb {
  pub vars: Vec<Var>,
  pub consts: Vec<Const>,
  pub hyps: Vec<Hypothesis>,
  pub asserts: Vec<Assertion>,
}

impl MmDb {
  pub fn new() -> MmDb {
    return MmDb {
      vars: Vec::new(),
      consts: Vec::new(),
      hyps: Vec::new(),
      asserts: Vec::new(),
    }
  }
  pub fn add_const(&mut self, name: String) -> u32 {
    let id = self.consts.len() as u32;
    self.consts.push(Const { name: name });
    return id;
  }

  pub fn add_variable(&mut self, name: String) -> u32 {
    let id = self.vars.len() as u32;
    self.vars.push(Var { name: name, type_declared: false, t: 0 });
    return id;
  }

  pub fn add_floating(&mut self, t: u32, var: u32) -> u32 {
    // We impose an additional constraint that variables never have different
    // types in different scopes. Really, variable declarations should be the same
    // as floating declarations, as there is no context in which you can use a variable
    // without a type.
    if self.vars[var as usize].type_declared {
      if self.vars[var as usize].t != t {
        panic!("invalid");
      }
    } else {
      self.vars[var as usize].type_declared = true;
      self.vars[var as usize].t = t;
    }

    let id = self.hyps.len();
    self.hyps.push(Hypothesis::F(VarDecl { t, var }));
    return id as u32;
  }

  pub fn add_essential(&mut self, t: u32, syms: Vec<Symbol>) -> u32 {
    let id = self.hyps.len();
    self.hyps.push(Hypothesis::E(SymStr { t, syms }));
    return id as u32;
  }

  pub fn add_axiom(&mut self,
    name: String,
    hyps: Vec<Hypothesis>,
    consequent: SymStr,
    disjoint_vars: Vec<(u32, u32)>)
    -> u32
  {
    let assert_id = self.asserts.len() as u32;
    self.asserts.push(Assertion {
      name: name,
      is_axiom: true,
      hyps: hyps,
      consequent: consequent,
      disjoint_vars: disjoint_vars,
      deps: vec![],
      proof: vec![],
    });

    return assert_id;
  }

  pub fn add_theorem(&mut self,
    name: String,
    hyps: Vec<Hypothesis>,
    consequent: SymStr,
    disjoint_vars: Vec<(u32, u32)>,
    deps: Vec<Symbol>,
    proof: Vec<ProofStep>)
    -> u32
  {
    

    let theorem = Assertion {
      name: name,
      is_axiom: false,
      hyps: hyps,
      consequent: consequent,
      disjoint_vars: disjoint_vars,
      deps,
      proof: proof,
    };

    self.check_proof_validity(&theorem);

    let assert_id = self.asserts.len() as u32;
    self.asserts.push(theorem);

    return assert_id;
  }

  /* NOTE: we assume that all optional variables are disjoint.
   */
  /**Apply an assertion to the stack. This will pop off hypotheses for the
   * assertion and then push the assertion (with the necessary variable
   * substitutions) to the stack. It will also check that the disjoint requirements
   * of the assertion are maintained, and perform necessary type and match checking
   * for the hypotheses.
   */
  fn apply(stack: &mut Vec<SymStr>, assert: &Assertion,
    mand_vars: &HashSet<u32>,
    disjoint_vars: &HashSet<(u32, u32)>)
  {
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
        Hypothesis::F(decl) => {
          if stack_entry.t != decl.t {
            panic!("invalid");
          }
          var_map.insert(decl.var, stack_entry.syms.clone());
        },
        Hypothesis::E (ss)     => {
          if stack_entry.t != ss.t {
            panic!("invalid");
          }

          // TODO: unnecessary allocation?
          let mut ss_sub = Vec::<Symbol>::new();
          for sym in ss.syms.iter() {
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
    for (v, syms) in var_map.iter() {
      if !mand_vars.contains(v) {
        continue;
      }
      for s in syms {
        if s.t == SymbolType::Var {
          if !mand_vars.contains(&s.id) {
            continue;
          }
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
    for (a, b) in &assert.disjoint_vars {
      if !mand_vars.contains(a) || !mand_vars.contains(b) {
        continue;
      }
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

  

  /**NOTE: this 'should' return bool, but it is a lot easier to trace and debug stuff
   * if you just panic.
   */
  fn check_proof_validity(&self, theorem: &Assertion)
  {
    let mut disjoint_var_set = HashSet::<(u32, u32)>::new();
    for (a, b) in theorem.disjoint_vars.iter() {
      disjoint_var_set.insert((*a, *b));
    }

    let mut stack = Vec::<SymStr>::new();
    let mut saved_statements = Vec::<SymStr>::new();
    let mand_vars = theorem.get_mand_var_set();

    for step in theorem.proof.iter() {
      match step {
        ProofStep::Hyp(id) => {
          let hyp = &theorem.hyps[*id as usize];
          stack.push(hyp.to_ss());
        },
        ProofStep::Dep(id) => {
          let sym = &theorem.deps[*id as usize];
          match sym.t {
            SymbolType::Hyp => {
              let hyp = &self.hyps[sym.id as usize];
              stack.push(hyp.to_ss());
            },
            SymbolType::Assert => {
              let assert = &self.asserts[sym.id as usize];
              MmDb::apply(&mut stack, assert, &mand_vars, &disjoint_var_set);
              saved_statements.push(stack[stack.len()-1].clone());
            },
            _ => panic!("invalid"),
          }
        },
        ProofStep::Saved(id) => {
          let st = saved_statements[*id as usize].clone();
          stack.push(st);
        },
      }
    }

    // check that top of stack matches consequent
    if stack.len() != 1 {
      panic!("invalid");
    }
    // check that top of stack is same as assertion, then create assertion
    if theorem.consequent.syms.len() != stack[0].syms.len() {
      panic!("invalid");
    }
    if theorem.consequent.t != stack[0].t {
      panic!("invalid");
    }
    for i in 0..theorem.consequent.syms.len() {
      if theorem.consequent.syms[i] != stack[0].syms[i] {
        panic!("invalid");
      }
    }
    return;
  }

  // Rendering functions
  
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
      for (i, hyp) in assert.hyps.iter().enumerate() {
        let ss = hyp.to_ss();
        println!("\th{}: {}", i, self.render_ss(&ss));
      }
      println!("\t{}", self.render_ss(&assert.consequent));
    }
  }

  fn render_decl(&self, decl: &VarDecl) -> String {
    return format!("$f {} {} $.",
      self.consts[decl.t as usize].name, self.vars[decl.var as usize].name);
  }

  fn render_hyp(&self, hyp: &Hypothesis) -> String {
    match hyp {
      Hypothesis::F(decl) => {
        return format!("$f {} {} $.",
          self.consts[decl.t as usize].name, self.vars[decl.var as usize].name);
      },
      Hypothesis::E(ss) => {
        return format!("$e {} $.", self.render_ss(ss));
      },
    }
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

  fn print_assert(&self, assert: &Assertion) {
    println!("${{");

    // disjoints
    for (a, b) in assert.disjoint_vars.iter() {
      println!("\t$d {} {} $.", self.vars[*a as usize].name, self.vars[*b as usize].name);
    }
    // TODO: we could go through the proof and determine which are necessary.
    let mut opt_vars = Vec::<u32>::new();
    for dep in assert.deps.iter() {
      if SymbolType::Hyp == dep.t {
        if let Hypothesis::F(decl) = &self.hyps[dep.id as usize] {
          opt_vars.push(decl.var);
        }
      }
    }
    if opt_vars.len() > 0 {
      // all optional variables are distinct from each other.
      if opt_vars.len() > 1 {
        print!("\t$d");
        for var in opt_vars.iter() {
          print!(" {}", self.vars[*var as usize].name);
        }
        println!(" $.");
      }
      // all optional variables are distinct from each mandatory variable
      let mand_vars = assert.get_mand_var_set();
      for mand_var in mand_vars.iter() {
        print!("\t$d {}", self.vars[*mand_var as usize].name);
        for var in opt_vars.iter() {
          print!(" {}", self.vars[*var as usize].name);
        }
        println!(" $.");
      }
    }

    // optional hypotheses
    for (i, d) in assert.deps.iter().enumerate() {
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
      for (i, d) in assert.deps.iter().enumerate() {
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
      let deps_len = assert.deps.len() as u32;

      // Perform 'compression' for Metamath format.
      // Only dependency statements that are referenced later
      // should get a Z, and then reference numbers need to be renumbered
      // to not include the unused intermediates.
      let mut depended_on = Vec::<bool>::new();
      for step in assert.proof.iter() {
        match step {
          ProofStep::Dep(id) => {
            if assert.deps[*id as usize].t == SymbolType::Assert {
              depended_on.push(false);
            }
          },
          ProofStep::Saved(id) => {
            depended_on[*id as usize] = true;
          },
          _ => {},
        }
      }
      let mut saved_id_to_num = Vec::<u32>::new();
      let mut dep_cnt = 0;
      for dep in depended_on.iter() {
        if *dep {
          saved_id_to_num.push(dep_cnt + hyps_len + deps_len);
          dep_cnt += 1;
        } else {
          saved_id_to_num.push(0);
        }
      }

      // print proof itself
      let mut assert_cnt = 0;
      for step in assert.proof.iter() {
        match step {
          ProofStep::Hyp(id) => {
            print!("{}", MmDb::num_to_mm_enc(*id));
          },
          ProofStep::Dep(id) => {
            print!("{}", MmDb::num_to_mm_enc(*id + hyps_len));
            if assert.deps[*id as usize].t == SymbolType::Assert {
              if depended_on[assert_cnt] {
                print!("Z");
              }
              assert_cnt += 1;
            }
          },
          ProofStep::Saved(id) => {
            print!("{}", MmDb::num_to_mm_enc(saved_id_to_num[*id as usize]));
          },
        }
      }

      println!(" $.");
    }
    println!("$}}");
  }

  pub fn print_mm(&self) {
    println!("$( constants $)");
    for c in self.consts.iter() {
      println!("\t$c {} $.", c.name);
    }
    println!("$( variables $)");
    for v in self.vars.iter() {
      println!("\t$v {} $.", v.name);
    }
    for assert in self.asserts.iter() {
      self.print_assert(assert);
    }
  }

  fn get_assert_types(&self) {
    let mut types = HashSet::<u32>::new();
    for assert in self.asserts.iter() {
      types.insert(assert.consequent.t);
    }
    for id in types.iter() {
      println!("{} ({})", self.consts[*id as usize].name, id);
    }
  }
}
