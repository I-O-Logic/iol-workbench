iol = new function() { const lib = this;

  /////////////////////
  // in-outset operations
  /////////////////////
  lib.out1 = function(A, N, x, throughput) {
    const N2 = getDirectlyTriggeredNorms(A,N)
    const M = heads(N2)
    if (_.isUndefined(throughput) || throughput === false) {
      // without throughput
      return pltk.consequence(M, x)
    } else {
      // with throughput
      return pltk.consequence(M.concat(A), x)
    }
  }
  
  lib.out2 = function(A, N, x, throughput) {
    if (_.isUndefined(throughput) || throughput === false) {
      // without throughput
      const cnfN = _.map(N, function(n) { return [pltk.conjs(pltk.cnf(body(n))), head(n)] })
      const dnf = pltk.disjs(pltk.dnf(pltk.mkConjs(A)))
      return _.every(dnf, function(clause) {
        const triggeredNorms = getBasicTriggeredNorms([clause],cnfN )
        return pltk.consequence(heads(triggeredNorms), x)
      });
    } else {
      // with throughput
      const m = materialization(N)
      return pltk.consequence(m.concat(A), x)
    }
  }
  
  lib.out3 = function(A, N, x, throughput) {
    // Select trigger function: Include A if with throughput
    let outputTriggered = function() { return pltk.consequence(heads(N2),x) }
    if (throughput === true) {
      outputTriggered = function() { return pltk.consequence(heads(N2).concat(A),x) }
    }
    // main function
    let A2 = A.slice()
    let N2 = getDirectlyTriggeredNorms(A,N)
    let NN = _.without(N, ...N2)
    while (!outputTriggered()) {
      A2 = A2.concat(heads(N2))
      let M = getDirectlyTriggeredNorms(A2, NN)
      if (_.isEmpty(M)) {
        return false
      } else {
        N2 = N2.concat(M)
        NN = _.without(NN, ...M)
      }
    }
    return true
  }
  
  lib.out4 = function(A, N, x, throughput) {
    if (_.isUndefined(throughput) || throughput === false) {
      // without throughput
      const cnfN = _.map(N, function(n) { return [pltk.conjs(pltk.cnf(body(n))), head(n)] })
      const dnf = pltk.disjs(pltk.dnf(pltk.mkConjs(A)))
      return _.every(dnf, function(clause) {
        const triggeredNorms = getBasicTriggeredNorms([clause],cnfN )
        let A2 = [clause]
        const N3 = _.map(N2, function(n) {
          return [_.reject(body(n), x => pltk.consequence([clause], x)),head(n)]
        });
        //console.log("N3", N3)
        const N4 = _.filter(N3, n => _.isEmpty(body(n)))
        const N5 = _.without(N3, ...N4)
        const N6 = _.filter(N5, function(n) {
            console.log("check (",pltk.plprintset(body(n)),pltk.plprint(head(n)),")")
            const compat = lib.getCompatibleNorms(N5,n)
            console.log("compat of this: ", _.map(compat, lib.printnorm))
            const compatBodies = _.map(compat, m => pltk.mkConjs(body(m)))
            console.log("compatbodies: ", _.map(compatBodies, pltk.plprint))
            const together = pltk.mkDisjs(compatBodies)
            console.log("together: ", pltk.plprint(together))
            return pltk.tautology(together)
          })
        const NN = _.without(N5, ...N6)
        if (pltk.consequence(heads(N4).concat(heads(N6)), x)) {
          return true
        } else {
          A2 = A2.concat(heads(N4).concat(heads(N6)))
          A3 = pltk.disjs(pltk.dnf(pltk.mkConjs(A2)))
          return _.every(A3, function(y2) {
            const M = _.map(NN, function(n) {
              return [_.reject(body(n), x => pltk.consequence([y2], x)),head(n)]
            });
            const M2 = _.filter(M, n => _.isEmpty(body(n)))
        const M3 = _.without(M, ...M2)
        const M4 = _.filter(M3, function(n) {
            console.log("check (",pltk.plprintset(body(n)),pltk.plprint(head(n)),")")
            const compat = lib.getCompatibleNorms(M3,n)
            console.log("compat of this: ", _.map(compat, lib.printnorm))
            const compatBodies = _.map(compat, m => pltk.mkConjs(body(m)))
            console.log("compatbodies: ", _.map(compatBodies, pltk.plprint))
            const together = pltk.mkDisjs(compatBodies)
            console.log("together: ", pltk.plprint(together))
            return pltk.tautology(together)
          })
           const together = M2.concat(M4)
           if (together.length == 0) return false
           else {
            return lib.out4([y2],N,x)
           }
          })
        }
      })
    } else {
      // with throughput: same as out2 with throughput
      return lib.out2(A,N,x,throughput)
    }
  }
  
  /* This is a prototypical implementation. This can be made much more elegant: TODO */
  lib.out4Old2 = function(A, N, x, throughput) {
    if (_.isUndefined(throughput) || throughput === false) {
      // without throughput
      const N2 = _.map(N, function(n) { return [pltk.conjs(pltk.cnf(body(n))), head(n)] })
      const dnf = pltk.disjs(pltk.dnf(pltk.mkConjs(A)))
      return _.every(dnf, function(clause) {
        let A2 = [clause]
        const N3 = _.map(N2, function(n) {
          return [_.reject(body(n), x => pltk.consequence([clause], x)),head(n)]
        });
        //console.log("N3", N3)
        const N4 = _.filter(N3, n => _.isEmpty(body(n)))
        const N5 = _.without(N3, ...N4)
        const N6 = _.filter(N5, function(n) {
            console.log("check (",pltk.plprintset(body(n)),pltk.plprint(head(n)),")")
            const compat = lib.getCompatibleNorms(N5,n)
            console.log("compat of this: ", _.map(compat, lib.printnorm))
            const compatBodies = _.map(compat, m => pltk.mkConjs(body(m)))
            console.log("compatbodies: ", _.map(compatBodies, pltk.plprint))
            const together = pltk.mkDisjs(compatBodies)
            console.log("together: ", pltk.plprint(together))
            return pltk.tautology(together)
          })
        const NN = _.without(N5, ...N6)
        if (pltk.consequence(heads(N4).concat(heads(N6)), x)) {
          return true
        } else {
          A2 = A2.concat(heads(N4).concat(heads(N6)))
          A3 = pltk.disjs(pltk.dnf(pltk.mkConjs(A2)))
          return _.every(A3, function(y2) {
            const M = _.map(NN, function(n) {
              return [_.reject(body(n), x => pltk.consequence([y2], x)),head(n)]
            });
            const M2 = _.filter(M, n => _.isEmpty(body(n)))
        const M3 = _.without(M, ...M2)
        const M4 = _.filter(M3, function(n) {
            console.log("check (",pltk.plprintset(body(n)),pltk.plprint(head(n)),")")
            const compat = lib.getCompatibleNorms(M3,n)
            console.log("compat of this: ", _.map(compat, lib.printnorm))
            const compatBodies = _.map(compat, m => pltk.mkConjs(body(m)))
            console.log("compatbodies: ", _.map(compatBodies, pltk.plprint))
            const together = pltk.mkDisjs(compatBodies)
            console.log("together: ", pltk.plprint(together))
            return pltk.tautology(together)
          })
           const together = M2.concat(M4)
           if (together.length == 0) return false
           else {
            return lib.out4([y2],N,x)
           }
          })
        }
      })
    } else {
      // with throughput: same as out2 with throughput
      return lib.out2(A,N,x,throughput)
    }
  }
  
  lib.out4Old = function(A, N, x, throughput) {
    if (_.isUndefined(throughput) || throughput === false) {
      // without throughput
      const dnf = pltk.disjs(pltk.dnf(pltk.mkConjs(A)))
      return dnf.every(function(y) {
        let A3 = [y]
        let N2 = getDirectlyTriggeredNorms(A3,N)
        let NN = _.without(N, ...N2)
        if (!pltk.consequence(heads(N2),x)) {
          A3 = A3.concat(heads(N2))
          A4 = pltk.disjs(pltk.dnf(pltk.mkConjs(A3)))
          return A4.every(function(y2) {
            let M = NN.filter(n => pltk.consequence([y2], n[0]))
            if (M.length == 0) return false
            else {
              return lib.out4([y2],N,x)
            }
          })
        } else return true
      })
    } else {
      // with throughput: same as out2 with throughput
      return lib.out2(A,N,x,throughput)
    }
  }
  

  
  /////////////////////
  // outset operations
  /////////////////////
  
  
  lib.out1set = function(A, N, throughput) {
    const N2 = getDirectlyTriggeredNorms(A,N)
    const M = heads(N2)
    if (_.isUndefined(throughput) || throughput === false) {
      // without throughput
      return semanticalInterreduce(M)
    } else {
      // with throughput
      return semanticalInterreduce(M.concat(A))
    }
  }
  
  lib.out2set = function(A, N, throughput) {
    if (_.isUndefined(throughput) || throughput === false) {
      // without throughput
      const cnfN = _.map(N, function(n) { return [pltk.conjs(pltk.cnf(body(n))), head(n)] })
      const dnf = pltk.disjs(pltk.dnf(pltk.mkConjs(A)))
      const triggeredEach = _.map(dnf, clause => heads(getBasicTriggeredNorms([clause],cnfN)))
      const result = _.reduce(triggeredEach, lib.semanticalIntersection)
      return semanticalInterreduce(result)
    } else {
      // with throughput
      const m = materialization(N)
      return semanticalInterreduce(m.concat(A))
    }
  }
  
  lib.out3set = function(A, N, throughput) {
    let A2 = A.slice() // the incremental set of facts
    let N2 = getDirectlyTriggeredNorms(A2,N) // the set of triggered norms
    let NN = _.without(N, ...N2) // The set of not-triggered norms
    let New = N2 // newly triggered norms
    while (!_.isEmpty(New)) { // terminate if no new norms can be triggered
      A2 = A2.concat(heads(N2)) // add facts
      New = getDirectlyTriggeredNorms(A2, NN) // potentially new triggered norms
      N2 = N2.concat(New) //add to result set
      NN = _.without(NN, ...New) // remove triggered from NN
    }
    if (_.isUndefined(throughput) || throughput === false) {
      return semanticalInterreduce(heads(N2))
    } else {
      return semanticalInterreduce(heads(N2).concat(A))
    }
  }
  
  lib.out4set = function(A, N, throughput) {
    if (_.isUndefined(throughput) || throughput === false) {
      // without throughput
      let lastOut = [{ op: 'LT', args: [] }]
      let basicOut = lib.out2set(A,N)
      let triggered = basicOut.concat(lib.out3set(A.concat(basicOut), N))
      
      while (!pltk.consequence(lastOut, pltk.mkConjs(triggered))) {
        lastOut = triggered
        basicOut = triggered.concat(lib.out2set(lastOut,N))
        triggered = basicOut.concat(lib.out3set(A.concat(basicOut), N))
      }
      
      return semanticalInterreduce(lastOut)
    } else {
      // with throughput
      return lib.out2set(A,N, throughput)
    }
  }
  
  /////////////////////
  // cIOL operations
  /////////////////////
  
  // Constrained IOL
  lib.maxFamily = function(out,N,A,C,throughput) {
    let NN = [N]
    let result = []
    
    //console.log("N", N)
    //console.log("NN", NN)
    //console.log("A", A)
    //console.log("C", C)
       
    while (!(_.isEmpty(NN))) {
      //console.log("####")
      const n0 = _.size(_.sample(NN))
      //console.log("n0", n0)
      //console.log("NN[0]", NN[0])
      NNC = _.filter(NN, function(x) {
        //console.log("x", x)
        return pltk.consistent(out(A,x, throughput).concat(C))
      })
      //console.log("NNC", NNC)
      result = _.concat(result, NNC)
      NNNotC = _.without(NN,NNC)
      //console.log("NNNotC", NNNotC)
      
      NN = _.uniqWith(_.flatMap(NNNotC,subsetsOneSmaller), _.isEqual)
      //console.log("subsets of NN", NN)
      NN = _.filter(NN, function(n) {return !_.some(result, r => subset(n,r))})
      //console.log("NN", NN)
    }
    return result
  }
  
  lib.outFamily = function(out,N,A,C,throughput) {
    const maxfam = lib.maxFamily(out,N,A,C, throughput)
    return _.map(maxfam, x => out(A, x, throughput))
  }
  lib.outFamily0 = function(out, NN, A,throughput) {
    return _.map(NN, x => out(A, x, throughput))
  }
  
  lib.credolousNetOutput = function(outFamily) {
    return semanticalInterreduce(_.unionWith(...outFamily, _.isEqual))
  }
  
  lib.skepticalNetOutput = function(outFamily) {
    const N0 = _.map(outFamily, N => pltk.mkConjs(N))
    return semanticalInterreduce([pltk.mkDisjs(N0)])
    //return semanticalInterreduce(_.reduce(NN, lib.semanticalIntersection))
  }
  
  lib.prefFamily = function(maxFamily, N, lifting) {
    const preference = makeIndexBasedPreference(N)
    const liftedPreference = lifting(preference)
    const prefFamily = getMaximals(maxFamily, liftedPreference)
    return prefFamily
  }
  
  const getMaximals = function(set, pref) {
    let result = []
    _.forEach(set, function(elem) {
      let rest = _.without(set,elem)
      if (!_.some(rest, e => pref(e,elem))) {
        result.push(elem)
      }
    });
    return result
  }
  
  const makeIndexBasedPreference = function(N) {
    /* returns: true if a is at least as strong as b,
                false otherwise. */
    return function(a,b) {
      const aIdx = _.findIndex(N, n => _.isEqual(n,a))
      const bIdx = _.findIndex(N, n => _.isEqual(n, b))
      if (aIdx == -1 || bIdx == -1) {
        return false
      } else {
        return bIdx - aIdx >= 0
      }
    }
  }
  
  const makeStrictPreference = function(pref) {
    return function(a,b) {
      if (pref(a,b)) {
        return !pref(b,a)
      } else {
        return false
      }
    }
  }
  
  lib.brasslifting = function(pref) {
    return function(A,B) {
      const diff1 = _.without(B, ...A)
      const diff2 = _.without(A, ...B)
      return _.every(diff1, n => _.some(diff2, m => pref(m,n)))
    }
  }
  
  lib.fafalifting = function(pref) {
    return function(A,B) {
      return _.every(A, n => _.every(B, m => pref(n,m)))
    }
  }
  
  /////////////////////
  // Utility
  /////////////////////
  
  const getDirectlyTriggeredNorms = function(A,N) {
    return _.filter(N, n => pltk.consequence(A, n[0]))
  }
  const body = function(n) { return n[0] }
  const bodies = function(N) { return _.map(N, body) }
  const head = function(n) { return n[1] }
  const heads = function(N) { return _.map(N, head) }
  const materialization = function(N) {
    return _.map(N, n => pltk.mkDisjs([pltk.mkNot(body(n)),head(n)]))
  }
  
  const subset = function(a,b) {
    return _.difference(a, b).length === 0
  }
  
  const subsetsOneSmaller = function(S) {
    let result = []
    S.forEach(s => 
      result.push(_.without(S,s))
    )
    return result
  }
  
  const canonizeOut = function(M) {
    let Msimp = pltk.simpset(M)
    // console.log(pltk.plprintset(Msimp))
    let together = pltk.mkConjs(Msimp)
    // console.log(pltk.plprint(together))
    let cnf = pltk.cnf(together)
    // console.log(cnf,pltk.plprint(cnf))
    let cnfSimp = pltk.cnfsimp(cnf)
    // console.log(cnfSimp, pltk.plprint(cnfSimp))
    let result = pltk.conjs(cnfSimp)
    return result
  }
  
  /** Assumes the bodies of N are CNF-normal sets of clauses */
  const getBasicTriggeredNorms = function(A, N) {
    const updatedN = _.map(N, function(n) {
      return [_.reject(body(n), x => pltk.consequence(A, x)),head(n)]
    });
    const directlyTriggered = _.filter(updatedN, n => _.isEmpty(body(n)))
    const others = _.without(updatedN, ...directlyTriggered)
    // for each norm:
    // get compatible norms (compatible head) [including itself?]
    // and check if the set of compatible norms has the success condition
    // filter all with that success condition
    const basicTriggered = _.filter(others, function(n) {
      //console.log("check (",pltk.plprintset(body(n)),pltk.plprint(head(n)),")")
      const compat = lib.getCompatibleNorms(others,n)
      ///console.log("compat of this: ", _.map(compat, lib.printnorm))
      const compatBodies = _.map(compat, m => pltk.mkConjs(body(m)))
      //console.log("compatbodies: ", _.map(compatBodies, pltk.plprint))
      const together = pltk.mkDisjs(compatBodies)
      //console.log("together: ", pltk.plprint(together))
      return pltk.tautology(together)
    })
    return directlyTriggered.concat(basicTriggered)
  }
  
  lib.partition = function(N) {
    const N2 = _.reduce(N, function(result, norm) {
      const h = head(norm);
      //console.log(h);
      let idx = _.find(result, function(n) {return _.some(n, x => pltk.equivalent(head(x),h))});
      //console.log(idx);
      if (_.isUndefined(idx)) {
        result.push([norm])
        //console.log("here")
      } else {
        idx.push(norm)
      }
      //console.log("result", result)
      return result;
    }, []);
    return N2
  }
  
  /* retrieve norms that have a head that is at least as strong as n */
  lib.getCompatibleNorms = function(N, n) {
    //console.log("getCompatibleNorms N: ", _.map(N, lib.printnorm))
    //console.log("getCompatibleNorms n: ", lib.printnorm(n))
    const h = head(n)
    const result = _.filter(N, m => pltk.consequence([head(m)],h))
    //console.log("getCompatibleNorms(N,n): ", _.map(result, lib.printnorm))
    return result
  }
  
  lib.semanticalIntersection = function(A,B) {
    let result = []
    _.forEach(A, function(a) {
      if (pltk.consequence(B,a)) {
        result.push(a)
      }
    })
    _.forEach(B, function(b) {
      if (pltk.consequence(A,b)) {
        result.push(b)
      }
    })
    //console.log("Result: ", pltk.plprintset(result))
    return result
  }
  
  /* TODO: unit propagation etc. for simplication */
  const semanticalInterreduce = function(A) {
    const Asimp = pltk.simpset(A)
    const Asimpcnf = pltk.conjs(pltk.cnfsimp(pltk.cnf(pltk.mkConjs(Asimp)))) 
    let result = []
    _.forEach(Asimpcnf, function(a) {
      if (!pltk.consequence(result,a)) {
        result = _.reject(result, r => pltk.consequence([a],r))
        result.push(a)
      }
    })
    //console.log("Result: ", pltk.plprintset(result))
    return result
  }
  
  lib.printnorm = function(n) {
    if (_.isArrayLike(body(n))) {
      return "(" + pltk.plprintset(body(n)) + "," + pltk.plprint(head(n)) + ")"
    } else {
      return "(" + pltk.plprint(body(n)) + "," + pltk.plprint(head(n)) + ")"
    }
  }
}

outfunction = iol.out1
outsetfunction = iol.out1set
throughput = false
constraints = false
netOutput = null
preferred = false
lifting = null
const negativeAnswer = "No, the formula x is not in the output set."
const positiveAnswer = "Yes, the formula x is in the output set."

N = null

$(document).ready(function() {
  // Examples
  $("#example1button").click(function(){
    $("input[type=text]").removeClass("is-invalid")
    $("#input").val('a,b')
    $("#norms").val('(a,x)\n(b,y)')
    //$("#norms").val('(a,x)\n(b,(x | y) & (x | ~y))')
    $("#constraints").val('')
    $("#output").val('x & y')
  });
  $("#example2button").click(function(){
    $("input[type=text]").removeClass("is-invalid")
    $("#input").val('a|b')
    $("#norms").val('(a,x)\n(b,x)')
    $("#constraints").val('')
    $("#output").val('x')
  });
  $("#example3button").click(function(){
    $("input[type=text]").removeClass("is-invalid")
    $("#input").val('a,b')
    $("#norms").val('(a,x)\n(b,y)\n(x&y,z)')
    $("#constraints").val('')
    $("#output").val('z')
  });
  $("#example4button").click(function(){
    $("input[type=text]").removeClass("is-invalid")
    $("#input").val('~helping')
    $("#norms").val('(T,helping)\n(helping,telling)\n(~helping,~telling)')
    $("#constraints").val('')
    $("#output").val('')
  });
  $("#example5button").click(function(){
    $("input[type=text]").removeClass("is-invalid")
    $("#input").val('killing')
    $("#norms").val('(T,~killing)\n(killing,killing & killingGently)')
    $("#constraints").val('')
    $("#output").val('')
  });
  $("#example6button").click(function(){
    $("input[type=text]").removeClass("is-invalid")
    $("#input").val('')
    $("#norms").val('(T,armyService | alternativeService)\n(T,~ armyService)')
    $("#constraints").val('')
    $("#output").val('')
  });


  // Parse error handling
  $("#input").on('input', function(e) {
    $("#input").removeClass("is-invalid")
  });
  $("#norms").on("input", function(event) {
    $("#norms").removeClass("is-invalid")
  });
  $("#constraints").on("input", function(event) {
    $("#constraints").removeClass("is-invalid")
  });
  $("#output").on("input", function(event) {
    $("#output").removeClass("is-invalid")
  });
  
  $('#checkbox-io-throughput').change(function() {
    if (this.checked) {
      throughput = true
    } else {
      throughput = false
    }
  })
  // GUI state
  $('#checkbox-constrained').change(function() {
    if (this.checked) {
      constraints = true
      $('#radio-net-credulous').prop("disabled", false);
      $('#radio-net-skeptical').prop("disabled", false);
      $('#checkbox-preferred-output').prop("disabled", false);
      if ($('#checkbox-preferred-output').prop("checked")) {
        $('#radio-preference-lifting-brass').prop("disabled", false);
        $('#radio-preference-lifting-fafa').prop("disabled", false);
      }
      if (netOutput == null) {
        $('#radio-net-credulous').click()
      }
      $('#constraints').prop("disabled", false);
      $('#copy-constraints').prop("disabled", false);
    } else {
      constraints = false
      $('#radio-net-credulous').prop("disabled", true);
      $('#radio-net-skeptical').prop("disabled", true);
      $('#checkbox-preferred-output').prop("disabled", true);
      $('#radio-preference-lifting-brass').prop("disabled", true);
      $('#radio-preference-lifting-fafa').prop("disabled", true);
      $('#constraints').prop("disabled", true);
      $('#copy-constraints').prop("disabled", true);
    }
  });
  $('input[type=radio][name=io-constrained-net]').change(function() {
    switch (this.value) {
      case "net-skeptical": netOutput = iol.skepticalNetOutput; break;
      case "net-credulous": netOutput = iol.credolousNetOutput; break;
      default:
        alert("This should not happen; tell Alex :-)")
        // should not happen
    }
  });
  $('input[type=radio][name=out]').change(function() {
    switch (this.value) {
      case "out1": outfunction = iol.out1;outsetfunction = iol.out1set; break;
      case "out2": outfunction = iol.out2;outsetfunction = iol.out2set; break;
      case "out3": outfunction = iol.out3;outsetfunction = iol.out3set; break;
      case "out4": outfunction = iol.out4;outsetfunction = iol.out4set; break;
      default: 
        alert("This should not happen; tell Alex :-)")
        // should not happen
    }
  });
  $('#checkbox-preferred-output').change(function() {
    if (this.checked) {
      preferred = true;
      $('#radio-preference-lifting-brass').prop("disabled", false);
      $('#radio-preference-lifting-fafa').prop("disabled", false);
      if (lifting == null) {
        $('#radio-preference-lifting-brass').click()
      }
    } else {
      preferred = false;
      $('#radio-preference-lifting-brass').prop("disabled", true);
      $('#radio-preference-lifting-fafa').prop("disabled", true);
    }
  });
  $('input[type=radio][name=io-preference-lifting]').change(function() {
    switch (this.value) {
      case "lifting-brass": lifting = iol.brasslifting; break;
      case "lifting-fafa": lifting = iol.fafalifting; break;
      default: 
        alert("This should not happen; tell Alex :-)")
        // should not happen
    }
  });
  $("#copy-constraints").click(function(){
    $('#constraints').val($('#input').val())
  });
  
  
  const calculateOutput = function() {
    const Atext = $("#input").val()
    const Ntext = $("#norms").val()
    const Ctext = $('#constraints').val()
    const xtext = $("#output").val()
    
    let Aval = []
    let Nval = []
    let Cval = []
  
    if (Atext.length > 0) {
      try {
        Aval = Atext.split(',').map(plparse.read)
      } catch(err) {
        $('#input').addClass("is-invalid")
        return
      }
    }
    
    if (Ntext.length > 0) {
      try {
        Nval = Ntext.trim().split('\n').filter(y => y.length > 0).map(x => x.trim().slice(1,-1).split(',').map(plparse.read))
        N = Nval
      } catch(err) {
        $('#norms').addClass("is-invalid")
        return
      }
    }
    
    if (Ctext.length > 0) {
      try {
        Cval = Ctext.split(',').map(plparse.read)
      } catch(err) {
        $('#constraints').addClass("is-invalid")
        return
      }
    }
  
    if (constraints) {
      const maxFamily = iol.maxFamily(outsetfunction,Nval,Aval,Cval,throughput)
      console.log("maxFamily: ", _.map(maxFamily, mf => _.map(mf, iol.printnorm)), maxFamily)
      let outFamily = null
      if (preferred) {
        const prefFamily = iol.prefFamily(maxFamily, Nval, lifting) 
        console.log("prefFamily: ", _.map(prefFamily, pf => _.map(pf, iol.printnorm)), prefFamily)
        outFamily = iol.outFamily0(outsetfunction,prefFamily,Aval,throughput)
      } else {
        outFamily = iol.outFamily0(outsetfunction,maxFamily,Aval,throughput)
      }
      console.log("outFamily: ", _.map(outFamily, pltk.plprintset), outFamily)
      let result = netOutput(outFamily)
      console.log("netOutput: ", pltk.plprintset(result), result)
      return result
    } else {
      let result = outsetfunction(Aval,Nval, throughput)
      console.log("output: ", pltk.plprintset(result), result)
      return result
    }
  }
  
  // iol functionality
  $("#outputButton").click(function(){
    $("#output").removeClass("is-invalid")
    const output = calculateOutput()
    const resultText = pltk.plprintset(output)
    $("#output").val("Cn(".concat(resultText,")"))
  });
  
  $("#checkButton").click(function(){
    $('#response').removeClass("alert-success")
    $('#response').removeClass("alert-warning")
    $('#response').css('visibility', 'collapse');

    const xtext = $("#output").val()
    let xval = null
    
    try {
      xval = plparse.read(xtext)
    } catch(err) {
        $('#output').addClass("is-invalid")
        return
    }
    if (xval == null) {
      $('#output').addClass("is-invalid")
      return
    }
    const output = calculateOutput()
    const result = pltk.consequence(output,xval)
    if (result != null) {
      if (result) {
        $('#response').addClass("alert-success")
        $('#response-text').text(positiveAnswer)
      } else {
        $('#response').addClass("alert-warning")
        $('#response-text').text(negativeAnswer)
      }
      $('#response').css('visibility', 'visible');
      window.setTimeout(function() {$('#response').css('visibility', 'collapse');}, 5000);
    }
  });
  
  
});

