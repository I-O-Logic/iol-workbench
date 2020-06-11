/*
  I/O Logic Workbench: Automated Reasoner for I/O Logics
  Copyright (C) 2020 Alexander Steen <alexander.steen@uni.lu>

  This program is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <https://www.gnu.org/licenses/>.
*/

pltk = new function() { const lib = this;
  
  // ###############################
  /* Constructors and destructors, utility methods */
  // ###############################
  lib.mkNot = function(f) {
    if (f == null) return null
    return {op: '~', args: [f]}
  }
  lib.mkConjs = function(fs) {
    if (fs.length == 0) return {op: 'LT', args: []}
    const f = function(acc,value) {return {op: '&', args: [acc, value]} }
    return fs.reduce(f)
  }
  lib.mkDisjs = function(fs) {
    if (fs.length == 0) return {op: 'LF', args: []}
    const f = function(acc,value) {return {op: '|', args: [acc, value]} }
    return fs.reduce(f)
  }
  
  lib.conjs = function(f) {
    if (f == null) return null
    if (!f.op) return null
    if (f.op == '&') {
      let left = lib.conjs(f.args[0])
      let right = lib.conjs(f.args[1])
      return left.concat(right)
    } else {
      return [f]
    }
  }
  
  lib.disjs = function(f) {
    if (f == null) return null
    if (!f.op) return null
    if (f.op == '|') {
      let left = lib.disjs(f.args[0])
      let right = lib.disjs(f.args[1])
      return left.concat(right)
    } else {
      return [f]
    }
  }
  
  lib.vars = function(f) {
    if (f == null) return null
    if (!f.op) return null
    let pre = vars0(f)
    return [...new Set(pre)]
  }
  let vars0 = function(f) {
    if (f.op == 'Var') {
      return [f.args[0]]
    } else if (f.op == '~') {
      return lib.vars(f.args[0])
    } else if (f.op == '&') {
      return lib.vars(f.args[0]).concat(lib.vars(f.args[1]))
    } else if (f.op == '|') {
      return lib.vars(f.args[0]).concat(lib.vars(f.args[1]))
    } else {
      return []
    }
  }
  
  lib.plprint = function(f) { 
    if (f == null) return null
    if (!f.op) return null
    if (f.op == 'LT') {
      return 'T'
    } else if (f.op == 'LF') {
      return 'F'
    } else if (f.op == 'Var') {
      return f.args[0]
    } else if (f.op == '~') {
      return '~' + lib.plprint(f.args[0])
    } else {
      return ['(',lib.plprint(f.args[0]),f.op,lib.plprint(f.args[1]),')'].join(' ')
    }
  }
  
  lib.plprintset = function(fs) {
    return _.flatMap(fs, lib.plprint)
  }
  
  // ###############################
  /* Normal forms */
  // ###############################
  
  lib.nnf = function(f) {
    if (f == null) return null
    if (!f.op) return null
    if (f.op == '~') {
      let body = f.args[0]
      if (body.op == '&') {
        let l = body.args[0]
        let r = body.args[1]
        return { op: '|', args: [{op: '~', args: [l]}, {op: '~', args: [r]}].map(lib.nnf) }
      } else if (body.op == '|') {
        let l = body.args[0]
        let r = body.args[1]
        return { op: '&', args: [{op: '~', args: [l]}, {op: '~', args: [r]}].map(lib.nnf) }
      } else if (body.op == '~') {
        return body.args[0]
      } else if (body.op == 'LT') {
        return { op: 'LF', args: [] }
      } else if (body.op == 'LF') {
        return { op: 'LT', args: [] }
      } else return f
    } else if (f.op == 'Var') {
      return f
    } else {
      return {op: f.op, args: f.args.map(lib.nnf)}
    }
  }
  
  lib.cnf = function(f) {
    if (f == null) return null
    if (!f.op) return null
    let nnf = lib.nnf(f)
    return cnf0(nnf)
  }
  let cnf0 = function(f) {
    if (f.op == '&') {
      let l = cnf0(f.args[0])
      let r = cnf0(f.args[1])
      return { op: '&', args: [l,r]}
    } else if (f.op == '|') {
      let l = f.args[0]
      let r = f.args[1]
      if (l.op == '&') {
        return cnf0({ op: '&', args: [{op: '|', args: [l.args[0],r]}, {op: '|', args: [l.args[1],r]}]})
      } else if (r.op == '&') {
        return cnf0({ op: '&', args: [{op: '|', args: [l,r.args[0]]}, {op: '|', args: [l,r.args[1]]}]})
      } else {
        let lresult = cnf0(l)
        let rresult = cnf0(r)
        if (lresult.op == '&' || rresult.op == '&') {
          return cnf0({ op: '|', args: [lresult,rresult]})
        } else {
          return { op: '|', args: [lresult,rresult]}
        }
      }
    } else {
      return f
    } 
  }
  
  lib.dnf = function(f) {
    if (f == null) return null
    if (!f.op) return null
    let nnf = lib.nnf(f)
    return dnf0(nnf)
  }
  let dnf0 = function(f) {
    if (f.op == '|') {
      let l = dnf0(f.args[0])
      let r = dnf0(f.args[1])
      return { op: '|', args: [l,r]}
    } else if (f.op == '&') { 
      let l = f.args[0]
      let r = f.args[1]
      if (l.op == '|') {
        return dnf0({ op: '|', args: [{op: '&', args: [l.args[0],r]}, {op: '&', args: [l.args[1],r]}]})
      } else if (r.op == '|') {
        return dnf0({ op: '|', args: [{op: '&', args: [l,r.args[0]]}, {op: '&', args: [l,r.args[1]]}]})
      } else {
        let lresult = dnf0(l)
        let rresult = dnf0(r)
        if (lresult.op == '|' || rresult.op == '|') {
          return dnf0({ op: '&', args: [lresult,rresult]})
        } else {
          return { op: '&', args: [lresult,rresult]}
        }
      }
    } else {
      return f
    } 
  }
  
  // ###############################
  /* Simplifications */
  // ###############################
  /* In the following, the Xsimp and Xsetsimp are analogous, except that
     the first assumes a formula, and the latter a set of formulas.
     In case of conjsetsimp/disjsetsimp, the individial elements are interpreted
     as conjuncts/disjuncts.
  */
  
  /* simp/simpset eliminates double negations and T and F from formulas */
  lib.simpset = function(fs) {
    if (fs == null) return null
    return _.map(fs, lib.simp)
  }
  
  lib.simp = function(f) {
    if (f == null) return null
    if (!f.op) return null
    let result = simp0(f)
    if (JSON.stringify(result) == JSON.stringify(f)) return f
    else return lib.simp(result)
  }
  let simp0 = function(f) {
    if (f.op == '~') {
        let body = simp0(f.args[0])
        if (body.op == 'LT') return {op: 'LF', args: []}
        else if (body.op == 'LF') return {op: 'LT', args: []}
        else if (body.op == '~') return body.args[0]
        else return {op: '~', args: [body]}
      } else if (f.op == '&') {
        let l = simp0(f.args[0])
        let r = simp0(f.args[1])
        if (l.op == 'LT') return r
        else if (r.op == 'LT') return l
        else if (l.op == 'LF') return l
        else if (r.op == 'LF') return r
        else return {op: '&', args: [l,r]}
      } else if (f.op == '|') {
        let l = simp0(f.args[0])
        let r = simp0(f.args[1])
        if (l.op == 'LF') return r
        else if (r.op == 'LF') return l
        else if (l.op == 'LT') return l
        else if (r.op == 'LT') return r
        else return {op: '|', args: [l,r]}
      } else return f
  }
  
  /* 
    Given a formula in DNF, apply simp, apply conjsimp on each conjuntive clause and apply disjsetsimp on
    the simplified clause set.
  */
  lib.dnfsimp = function(dnf) {
    let dnf0 = lib.simp(dnf)
    let clauses = lib.disjs(dnf0)
    let clausesSimp = _.map(clauses, lib.conjsimp)
    console.log(clausesSimp, pltk.plprintset(clausesSimp))
    let result = lib.disjsetsimp(clausesSimp)
    console.log(result, pltk.plprintset(result))
    return lib.mkDisjs(result)
  }
  
  /* 
    Given a formula in CNF, apply simp, apply disjsimp on each disjunctive clause and apply conjsetsimp on
    the simplified clause set.
  */
  lib.cnfsimp = function(cnf) {
    let cnf0 = lib.simp(cnf)
    let clauses = lib.conjs(cnf0)
    let clausesSimp = _.map(clauses, lib.disjsimp)
    let result0 =  lib.conjsetsimp(clausesSimp)
    let result = lib.disjclausesetInterreduce(result0)
    return lib.mkConjs(result)
  }
  
  
  /* applies flat (shallow) intra-clause contractions:
     A,~A -> T; A,A -> A; T,X -> T; F,X -> X
    
     Assumes an n-ary disjunctive formula; for a list of formulas use lib.disjsetsimp.  */
  lib.disjsimp = function(f) {
    return lib.mkDisjs(lib.disjsetsimp(lib.disjs(f)))
  }
  
  lib.disjsetsimp = function(fs) {
    let lits0 = _.map(_.uniqWith(fs, _.isEqual), lib.simp)
    let lits = _.sortBy(lits0, ['args'])
    let lits1 = _.filter(lits, x => !lib.isF(x))
    let redundantLit = _.some(lits1, x => _.some(_.without(lits1,x), y => _.isEqual(y, lib.mkNot(x)) ))
    let tLit = _.some(lits1, lib.isT)
    if (redundantLit || tLit) {
      return [{op: 'LT', args: []}]
    } else {
      return lits1
    }
  }
  
  /* applies flat (shallow) intra-clause contractions:
     A,~A -> F; A,A -> A; F,X -> F; T,X -> X
    
     Assumes an n-ary conjective formula; for a list of formulas use lib.conjsetsimp.  */
  lib.conjsimp = function(f) {
    return lib.mkConjs(lib.conjsetsimp(lib.conjs(f)))
  }
  
  lib.conjsetsimp = function(fs) {
    let lits = _.map(_.uniqWith(fs, _.isEqual), lib.simp)
    let lits1 = _.filter(lits, x => !lib.isT(x))
    let redundantLit = _.some(lits1, x => _.some(_.without(lits1,x), y => _.isEqual(y, lib.mkNot(x)) ))
    let fLit = _.some(lits1, lib.isF)
    if (redundantLit || fLit) {
      return [{op: 'LF', args: []}]
    } else {
      return lits1
    }
  }
  
  /* remove subsumed disjunctive clauses from input set and propagate units for simplication*/
  lib.disjclausesetInterreduce = function(fs) {
    let P = []
    let U = fs.slice()
    while (!_.isEmpty(U)) {
      let g = _.sample(U)
      U = _.pull(U, g)
      if (_.some(P, x => lib.disjClauseSubsumes(x, g))) {
        /* skip */
      } else {
        P = _.filter(P, x => !lib.disjClauseSubsumes(g, x))
        if (lib.isUnitFormula(g)) {
          const lit = lib.getLitAsVar(g)
          const replaceBy = lib.getLitPolarity(g)
          
          // todo
        }
        P.push(g)
      }
    }
    return P
  }
  
  lib.disjClauseReplaceAll = function(clause, what, by) {
    const lits = pltk.disjs(clause)
    
  }
  
  lib.replaceBy = function(it,what,by) {
    if (_.isEqual(it, what)) {
      return by
    } else return it
  }
  
  
  /* true if a subsumes b */
  lib.disjClauseSubsumes = function(a,b) {
    let litsA = _.uniqWith(lib.disjs(a), _.isEqual)
    let litsB = _.uniqWith(lib.disjs(b), _.isEqual)
    return _.isEmpty(_.differenceWith(litsA,litsB, _.isEqual))
  }
  
  lib.isUnit = function(fs) {
    return _.size(fs) == 1
  }
  
  lib.isUnitFormula = function(f) {    
    if (lib.isNeg(f)) {
      const body = f.args[0]
      return lib.isVariable(body)
    } 
    return lib.isVariable(f)
  }
 
  lib.isVariable = function(f) {
    return _.get(f, 'op', '') == 'Var'
  }
  
  lib.isNeg = function(f) {
    return _.get(f, 'op', '') == '~'
  }
  
  lib.getLitPolarity = function(lit) {
    if (lib.isVariable(lit)) {
      return { op: 'LT', args: []}
    } else {
      return { op: 'LF', args: []}
    }
  }
  
  lib.getLitAsVar = function(lit) {
    if (lib.isVariable(lit)) {
      return lit
    } else {
      return lit.args[0]
    }
  }
 
  lib.isT = function(f) {
    return _.has(f,'op') && f.op == 'LT'
  }
  lib.isF = function(f) {
    return _.has(f,'op') && f.op == 'LF'
  }
  
  // ###############################
  /* Export to dimacs */
  // ###############################
  lib.todimacs = function(f) {
    if (f == null) return null
    
    let cnf = lib.cnf(f)
    let conjs = lib.conjs(cnf)
    let clauses = conjs.length
    let vars = lib.vars(cnf)
    
    let varToInt = function(x) {
      if (x.op == 'Var') {
        return vars.indexOf(x.args[0])+1
      } else return null
    }
    let clauseToLine = function(c) {
      let ctl0 = function(c) {
        if (c.op == 'Var') {
          return varToInt(c)
        } else if (c.op == '~') {
          return -varToInt(c.args[0])
        } 
      }
      let disjs = lib.disjs(c)
      let line  = disjs.map(ctl0)
      line.push(0)
      return line.join(" ")
    }
    
    let result = [`p cnf ${vars.length} ${clauses}`]
    conjs.forEach(function(x) {
      result.push(clauseToLine(x))
    })
    return result.join("\n")
  }
  
  lib.todimacsarray = function(f) {
    if (f == null) return null
    
    let simp = lib.simp(f)
    let cnf0 = lib.cnf(simp)
    let cnf = lib.cnfsimp(cnf0)
    
    if (cnf.op == 'LT') return []
    if (cnf.op == 'LF') return [[]]
    
    let conjs = lib.conjs(cnf)
    let clauses = conjs.length
    let vars = lib.vars(cnf)
    
    let varToInt = function(x) {
      if (x.op == 'Var') {
        return vars.indexOf(x.args[0])+1
      } else return null
    }
    let clauseToLine = function(c) {
      let ctl0 = function(c) {
        if (c.op == 'Var') {
          return varToInt(c)
        } else if (c.op == '~') {
          return -varToInt(c.args[0])
        } 
      }
      let disjs = lib.disjs(c)
      let line  = disjs.map(ctl0)
      return line
    }
    
    let result = []
    conjs.forEach(function(x) {
      result.push(clauseToLine(x))
    })
    return result
  }
  
  
  // ###############################
  /* Semantical functions */
  // ###############################
  lib.sat = function(f) {
    if (f == null) return null
    let vars = lib.vars(f)
    let clauses = lib.todimacsarray(f)
    if (clauses.length == 0) return true
    if (clauses.some(c => c.length == 0)) return false
    let result = satSolve(vars.length, clauses)
    return result
  }
  
  lib.unsat = function(f) {
    if (f == null) return null
    return !lib.sat(f)
  }
  
  lib.consistent = function(fs) {
    let formula = lib.mkConjs(fs)
    return lib.sat(formula)
  }
  
  lib.consequence = function(assumptions,f) {
    //console.log("consequence:", lib.plprintset(assumptions), lib.plprint(f))
    let formulas = assumptions.slice()
    formulas.push(lib.mkNot(f))
    return lib.unsat(lib.mkConjs(formulas))
  }
  
  lib.tautology = function(f) {
    return lib.unsat(lib.mkNot(f))
  }
  
  lib.equivalent = function(f,g) {
    //console.log("equivalent", pltk.plprint(f), pltk.plprint(g))
    const impl = lib.mkDisjs([lib.mkNot(f),g])
    const lpmi = lib.mkDisjs([lib.mkNot(g),f])
    return lib.tautology(lib.mkConjs([impl,lpmi]))
  }
 
}
