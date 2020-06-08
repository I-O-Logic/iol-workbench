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
  
  lib.out2Old = function(A, N, x, throughput) {
    if (_.isUndefined(throughput) || throughput === false) {
      // without throughput
      const dnf = pltk.disjs(pltk.dnf(pltk.mkConjs(A)))
      return dnf.every(y => lib.out1([y],N,x))
    } else {
      // with throughput
      const m = materialization(N)
      return pltk.consequence(m.concat(A), x)
    }
  }
  
  lib.out2 = function(A, N, x, throughput) {
    if (_.isUndefined(throughput) || throughput === false) {
      // without throughput
      const N2 = _.map(N, function(n) { return [pltk.conjs(pltk.cnf(body(n))), head(n)] })
      //console.log("N2", N2)
      const dnf = pltk.disjs(pltk.dnf(pltk.mkConjs(A)))
      return _.every(dnf, function(clause) {
        //console.log("clause", clause)
        const N3 = _.map(N2, function(n) {
          return [_.reject(body(n), x => pltk.consequence([clause], x)),head(n)]
        });
        //console.log("N3", N3)
        const N4 = _.filter(N3, n => _.isEmpty(body(n)))
        const NN = _.without(N3, ...N4)
        
        // for each norm:
        // get compatible norms (compatible head) [including itself?]
        // and check if the set of compatible norms has the success condition
        // filter all with that success condition
        const N6 = _.filter(NN, function(n) {
          console.log("check (",pltk.plprintset(body(n)),pltk.plprint(head(n)),")")
          const compat = lib.getCompatibleNorms(NN,n)
          console.log("compat of this: ", _.map(compat, lib.printnorm))
          const compatBodies = _.map(compat, m => pltk.mkConjs(body(m)))
          console.log("compatbodies: ", _.map(compatBodies, pltk.plprint))
          const together = pltk.mkDisjs(compatBodies)
          console.log("together: ", pltk.plprint(together))
          return pltk.tautology(together)
        })
        return pltk.consequence(heads(N4).concat(heads(N6)), x)
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
    let A2 = A.slice()
    let N2 = getDirectlyTriggeredNorms(A,N)
    let NN = _.without(N, ...N2)
    while (!outputTriggered()) {
      A2 = A2.concat(heads(N2))
      let M = getDirectlyTriggeredNorms(A2, NN)
      if (M.length == 0) {
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
  lib.out1set = function(A,N) {
    const N2 = getDirectlyTriggeredNorms(A,N)
    const M = heads(N2)
    return canonizeOut(M)
  }
  
  lib.out2set = function(A,N) {
    let dnf = pltk.disjs(pltk.dnf(pltk.mkConjs(A)))
    //console.log("clauses", pltk.plprintset(dnf))
    let Ns = _.map(dnf, x => lib.out1set([x],N))
    //console.log("Ns", Ns, _.map(Ns, pltk.plprintset))
    let result = _.intersectionWith(...Ns, _.isEqual)
    //console.log("result",pltk.plprintset(result))
    return result
  }
  
  lib.out3set = function(A,N) {
    let A2 = A.slice() // the incremental set of facts
    let N2 = N.filter(n => pltk.consequence(A2, n[0])) // the set of triggered norms
    let NN = _.without(N, ...N2) // The set of not-triggered norms
    let New = N2 // newly triggered norms
    while (!_.isEmpty(New)) { // terminate if no new norms can be triggered
      A2 = A2.concat(N2.map(n => n[1])) // add facts
      New = NN.filter(n => pltk.consequence(A2, n[0])) // potentially new triggered norms
      N2 = N2.concat(New) //add to result set
      NN = NN.filter(n => !New.includes(n)) // remove triggered from NN
    }
    return canonizeOut(N2.map(n => n[1]))
  }
  
  lib.out4set = function(A,N) {
    // take out2set
  }
  
  /////////////////////
  // cIOL operations
  /////////////////////
  
  // Constrained IOL
  lib.maxFamily = function(out,N,A,C) {
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
        return pltk.consistent(out(A,x).concat(C))
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
  
  lib.outFamily = function(out,N,A,C) {
    const maxfam = lib.maxFamily(out,N,A,C)
    return _.map(maxfam, x => out(A, x))
  }
  lib.outFamily0 = function(out, NN, A) {
    return _.map(NN, x => out(A, x))
  }
  
  lib.credolousNetOutput = function(NN) {
    return _.unionWith(...NN, _.isEqual)
  }
  
  lib.skepticalNetOutput = function(NN) {
    return _.intersectionWith(...NN, _.isEqual)
  }
  
  // Utility
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
  
  let subset = function(a,b) {
    return _.difference(a, b).length === 0
  }
  
  let subsetsOneSmaller = function(S) {
    let result = []
    S.forEach(s => 
      result.push(_.without(S,s))
    )
    return result
  }
  
  let canonizeOut = function(M) {
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
  
  lib.enrich = function(N) {
    const NN = lib.partition(N)
    
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
  
  lib.getCompatibleNorms = function(N, n) {
    console.log("getCompatibleNorms N: ", _.map(N, lib.printnorm))
    console.log("getCompatibleNorms n: ", lib.printnorm(n))
    const h = head(n)
    const result = _.filter(N, m => pltk.consequence([head(m)],h))
    console.log("getCompatibleNorms(N,n): ", _.map(result, lib.printnorm))
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
throughput = false
constraints = false
netOutput = null
preference = null
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
      if (netOutput == null) {
        $('#radio-net-credulous').click()
      }
      $('#constraints').prop("disabled", false);
      $('#copy-constraints').prop("disabled", false);
    } else {
      constraints = false
      $('#radio-net-credulous').prop("disabled", true);
      $('#radio-net-skeptical').prop("disabled", true);
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
      case "out1": outfunction = iol.out1; break;
      case "out2": outfunction = iol.out2; break;
      case "out3": outfunction = iol.out3; break;
      case "out4": outfunction = iol.out4; break;
      default: 
        alert("This should not happen; tell Alex :-)")
        // should not happen
    }
  });
  $("#copy-constraints").click(function(){
    $('#constraints').val($('#input').val())
  });
  
  
  // iol functionality
  $("#outputButton").click(function(){
    const Atext = $("#input").val()
    const Ntext = $("#norms").val()
    const Ctext = $('#constraints').val()
    
    let Aval = []
    let Nval = []
    let Cval = []
    
    if (Atext.length > 0) {
      Aval = Atext.split(',').map(plparse.read)
    }
    if (Ntext.length > 0) {
      Nval = Ntext.trim().split('\n').filter(y => y.length > 0).map(x => x.trim().slice(1,-1).split(',').map(plparse.read))
    }
    if (Ctext.length > 0) {
      Cval = Ctext.split(',').map(plparse.read)
    }
    
    let result = iol.out2set(Aval,Nval)
    console.log("result", result, pltk.plprintset(result))
    let resultText = pltk.plprintset(result)
    $("#output").val("Cn(".concat(resultText,")"))
    //console.log("consequence:", pltk.consequence(result, xval))
    //console.log("cval", pltk.plprintset(Cval))
    /*let result2 = iol.maxFamily(iol.out2set, Nval, Aval, Cval)
    console.log("result2", result2)
    let result3 = iol.outFamily0(iol.out2set, result2, Aval)
    console.log("result3", result3)
    let result4 = netOutput(result3)
    console.log("result4", result4, pltk.plprintset(result4))*/
  });
  
  $("#checkButton").click(function(){
    //$('#feedbackno').hide()
    //$('#feedbackyes').hide()
    $('#response').removeClass("alert-success")
    $('#response').removeClass("alert-warning")
    $('#response').css('visibility', 'collapse');

    const Atext = $("#input").val()
    const Ntext = $("#norms").val()
    const Ctext = $('#constraints').val()
    const xtext = $("#output").val()
    
    let Aval = []
    let Nval = []
    let Cval = []
    let xval = null
    
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
    
    /*
    let out = null
    if ($('#radio-out1').prop("checked")) {
      out = iol.out1
    } else if ($('#radio-out2').prop("checked")) {
      out = iol.out2
    } else if ($('#radio-out3').prop("checked")) {
      out = iol.out3
    } else if ($('#radio-out4').prop("checked")) {
      out = iol.out4
    }*/
    
    let result = outfunction(Aval,Nval,xval, throughput)
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

