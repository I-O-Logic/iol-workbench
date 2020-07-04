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

iol = new function() { const lib = this;
  
  /////////////////////
  // outset operations
  /////////////////////
  
  lib.out1set = function(A, N, throughput) {
    const triggered = getDirectlyTriggeredNorms(A,N)
    const M = heads(triggered)
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
      /* old implementation, TODO: Remove */
      //const cnfN = _.map(N, function(n) { return [pltk.conjs(pltk.cnf(body(n))), head(n)] })
      //const dnf = pltk.disjs(pltk.dnf(pltk.mkConjs(A)))
      //const triggeredEach = _.map(dnf, clause => heads(getBasicTriggeredNorms([clause],cnfN)))
      //const result = _.reduce(triggeredEach, lib.semanticalIntersection)
      //console.log(result, pltk.plprintset(result))
      /* old implementation END */
      const triggered = getBasicTriggeredNorms(A, N)
      const result = heads(triggered)
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
      
      // Loop: Terminate if the previous output implies the new one (then, nothing new has been detached)
      // The inverse (i.e., the new output implies the old one) holds unconditionally
      while (!pltk.consequence(lastOut, pltk.mkConjs(triggered))) {
        lastOut = triggered
        basicOut = triggered.concat(lib.out2set(lastOut,N))
        triggered = basicOut.concat(lib.out3set(A.concat(basicOut), N))
      }
      
      return semanticalInterreduce(lastOut)
    } else {
      // with throughput
      return lib.out2set(A, N, throughput)
    }
  }
  
  /////////////////////
  // cIOL operations
  /////////////////////
  
  // Constrained IOL
  lib.maxFamily = function(out,N,A,C,throughput) {
    let NN = [N]
    let result = []
       
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
  
  /*const canonizeOut = function(M) {
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
  }*/
  
  /** Assumes the bodies of N are CNF-normal sets of clauses, TODO: Remove */
  /*const getBasicTriggeredNormsOLD = function(A, N) {
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
  }*/
  
  const getBasicTriggeredNorms = function(A, N) {
    return _.filter(N, function(n) {
      //console.log("check (",pltk.plprintset(body(n)),pltk.plprint(head(n)),")")
      const compat = lib.getCompatibleNorms(N,n)
      ///console.log("compat of this: ", _.map(compat, lib.printnorm))
      const compatBodies = bodies(compat)
      //console.log("compatbodies: ", _.map(compatBodies, pltk.plprint))
      const together = pltk.mkDisjs(compatBodies)
      //console.log("together: ", pltk.plprint(together))
      return pltk.consequence(A, together)
    })
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

/* IOLW state */
const iolw = {
  'outfunction': iol.out1set,
  'throughput': false,
  'constaints': false,
  'netOutput': null,
  'preferred': false,
  'lifting': null
}

N = null

$(document).ready(function() {

  ///////////////////////////////////////////////////
  // Examples
  ///////////////////////////////////////////////////
  
  $("#example1button").click(function(){
    $("input[type=text]").removeClass("is-invalid")
    $("#input").val('a,b')
    $("#norms").val('(a,x)\n(b,y)')
    $("#constraints").val('')
    $("#output").val('x & y')
    $('#radio-out1').click()
    if ($('#checkbox-constrained').prop("checked", true)) {
      $('#checkbox-constrained').click()
    }
    if ($('#checkbox-preferred-output').prop("checked", true)) {
      $('#checkbox-preferred-output').click()
    }
  });
  $("#example2button").click(function(){
    $("input[type=text]").removeClass("is-invalid")
    $("#input").val('a|b')
    $("#norms").val('(a,x)\n(b,x)')
    $("#constraints").val('')
    $("#output").val('x')
    $('#radio-out2').click()
    if ($('#checkbox-constrained').prop("checked", true)) {
      $('#checkbox-constrained').click()
    }
    if ($('#checkbox-preferred-output').prop("checked", true)) {
      $('#checkbox-preferred-output').click()
    }
  });
  $("#example3button").click(function(){
    $("input[type=text]").removeClass("is-invalid")
    $("#input").val('a,b')
    $("#norms").val('(a,x)\n(b,y)\n(x&y,z)')
    $("#constraints").val('')
    $("#output").val('z')
    $('#radio-out3').click()
    if ($('#checkbox-constrained').prop("checked", true)) {
      $('#checkbox-constrained').click()
    }
    if ($('#checkbox-preferred-output').prop("checked", true)) {
      $('#checkbox-preferred-output').click()
    }
  });
  $("#example4button").click(function(){
    $("input[type=text]").removeClass("is-invalid")
    $("#input").val('~helping')
    $("#norms").val('(T,helping)\n(helping,telling)\n(~helping,~telling)')
    $("#constraints").val('~helping')
    $("#output").val('')
    $('#radio-out3').click()
    if ($('#checkbox-constrained').prop("checked", false)) {
      $('#checkbox-constrained').click()
    }
    if ($('#checkbox-preferred-output').prop("checked", true)) {
      $('#checkbox-preferred-output').click()
    }
  });
  $("#example5button").click(function(){
    $("input[type=text]").removeClass("is-invalid")
    $("#input").val('killing')
    $("#norms").val('(T,~killing)\n(killing,killing & killingGently)')
    $("#constraints").val('killing')
    $("#output").val('')
    $('#radio-out1').click()
    if ($('#checkbox-constrained').prop("checked", false)) {
      $('#checkbox-constrained').click()
    }
    if ($('#checkbox-preferred-output').prop("checked", true)) {
      $('#checkbox-preferred-output').click()
    }
  });
  $("#example6button").click(function(){
    $("input[type=text]").removeClass("is-invalid")
    $("#input").val('')
    $("#norms").val('(T,armyService | alternativeService)\n(T,~ armyService)')
    $("#constraints").val('')
    $("#output").val('')
    $('#radio-out1').click()
    if ($('#checkbox-constrained').prop("checked", false)) {
      $('#checkbox-constrained').click()
    }
    if ($('#checkbox-preferred-output').prop("checked", true)) {
      $('#checkbox-preferred-output').click()
    }
  });
  $("#example7button").click(function(){
    $("input[type=text]").removeClass("is-invalid")
    $("#input").val('')
    $("#norms").val('(T,cityA)\n(T,cityB)\n(T,cityC)')
    $("#constraints").val('(~cityA|(~cityB|~cityC)),(~cityA|~cityB)')
    $("#output").val('')
    if ($('#checkbox-constrained').prop("checked", false)) {
      $('#checkbox-constrained').click()
    }
    if ($('#checkbox-preferred-output').prop("checked", false)) {
      $('#checkbox-preferred-output').click()
    }
  });
  $("#example8button").click(function(){
    $("input[type=text]").removeClass("is-invalid")
    $("#input").val('dataset')
    $("#norms").val('(chemo,keepWBCcount)\n(dataset,chemo)\n(dataset,~chemo)')
    $("#constraints").val('dataset')
    $("#output").val('')
    $('#radio-out3').click()
    if ($('#checkbox-constrained').prop("checked", false)) {
      $('#checkbox-constrained').click()
    }
    if ($('#checkbox-preferred-output').prop("checked", false)) {
      $('#checkbox-preferred-output').click()
    }
  });
  $("#example9button").click(function(){
    $("input[type=text]").removeClass("is-invalid")
    $("#input").val('')
    $("#norms").val('(heatingOn,~windowOpen)\n(T,windowOpen)\n(T,heatingOn)')
    $("#constraints").val('')
    $("#output").val('')
    $('#radio-out3').click()
    if ($('#checkbox-constrained').prop("checked", false)) {
      $('#checkbox-constrained').click()
    }
    if ($('#checkbox-preferred-output').prop("checked", false)) {
      $('#checkbox-preferred-output').click()
    }
  });

  ///////////////////////////////////////////////////
  // Parse error handling
  ///////////////////////////////////////////////////
  
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
  
  ///////////////////////////////////////////////////
  // GUI state stuff
  ///////////////////////////////////////////////////

  /** Select the right out function */
  $('input[type=radio][name=out]').change(function() {
    switch (this.value) {
      case "out1": iolw.outfunction = iol.out1set; break;
      case "out2": iolw.outfunction = iol.out2set; break;
      case "out3": iolw.outfunction = iol.out3set; break;
      case "out4": iolw.outfunction = iol.out4set; break;
      default: 
        alert("This should not happen; tell Alex :-)")
        // should not happen
    }
  });
  
  /** Select the throughput setting */
  $('#checkbox-io-throughput').change(function() {
    if (this.checked) {
      iolw.throughput = true
    } else {
      iolw.throughput = false
    }
  })

  /** Select the contrained setting */
  $('#checkbox-constrained').change(function() {
    if (this.checked) {
      iolw.constraints = true
      $('#radio-net-credulous').prop("disabled", false);
      $('#radio-net-skeptical').prop("disabled", false);
      $('#checkbox-preferred-output').prop("disabled", false);
      if ($('#checkbox-preferred-output').prop("checked")) {
        $('#radio-preference-lifting-brass').prop("disabled", false);
        $('#radio-preference-lifting-fafa').prop("disabled", false);
      }
      if (iolw.netOutput == null) {
        $('#radio-net-credulous').click()
      }
      $('#constraints').prop("disabled", false);
      $('#copy-constraints').prop("disabled", false);
    } else {
      iolw.constraints = false
      $('#radio-net-credulous').prop("disabled", true);
      $('#radio-net-skeptical').prop("disabled", true);
      $('#checkbox-preferred-output').prop("disabled", true);
      $('#radio-preference-lifting-brass').prop("disabled", true);
      $('#radio-preference-lifting-fafa').prop("disabled", true);
      $('#constraints').prop("disabled", true);
      $('#copy-constraints').prop("disabled", true);
    }
  });
  
  /** Select the net output setting */
  $('input[type=radio][name=io-constrained-net]').change(function() {
    switch (this.value) {
      case "net-skeptical": iolw.netOutput = iol.skepticalNetOutput; break;
      case "net-credulous": iolw.netOutput = iol.credolousNetOutput; break;
      default:
        alert("This should not happen; tell Alex :-)")
        // should not happen
    }
  });
  
  /** Select the preferred output setting */
  $('#checkbox-preferred-output').change(function() {
    if (this.checked) {
      iolw.preferred = true;
      $('#radio-preference-lifting-brass').prop("disabled", false);
      $('#radio-preference-lifting-fafa').prop("disabled", false);
      if (iolw.lifting == null) {
        $('#radio-preference-lifting-brass').click()
      }
    } else {
      iolw.preferred = false;
      $('#radio-preference-lifting-brass').prop("disabled", true);
      $('#radio-preference-lifting-fafa').prop("disabled", true);
    }
  });
  
  /** Select the preferred output preference lifting setting */
  $('input[type=radio][name=io-preference-lifting]').change(function() {
    switch (this.value) {
      case "lifting-brass": iolw.lifting = iol.brasslifting; break;
      case "lifting-fafa": iolw.lifting = iol.fafalifting; break;
      default: 
        alert("This should not happen; tell Alex :-)")
        // should not happen
    }
  });
  
  /** Utility: Copy input as constraint in GUI */
  $("#copy-constraints").click(function(){
    $('#constraints').val($('#input').val())
  });
  
  ///////////////////////////////////////////////////
  // I/O button functionalities
  ///////////////////////////////////////////////////
  
  /**
    Returns the output set wrt. the given parameter settings.
    Result is a list of formulas.
  */
  const calculateOutput = function() {
    const Atext = $("#input").val()
    const Ntext = $("#norms").val()
    const Ctext = $('#constraints').val()
    
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
  
    if (iolw.constraints) {
      const maxFamily = iol.maxFamily(iolw.outfunction,Nval,Aval,Cval,iolw.throughput)
      console.log("maxFamily: ", _.map(maxFamily, mf => _.map(mf, iol.printnorm)), maxFamily)
      let outFamily = null
      if (iolw.preferred) {
        const prefFamily = iol.prefFamily(maxFamily, Nval, iolw.lifting) 
        console.log("prefFamily: ", _.map(prefFamily, pf => _.map(pf, iol.printnorm)), prefFamily)
        outFamily = iol.outFamily0(iolw.outfunction,prefFamily,Aval,iolw.throughput)
      } else {
        outFamily = iol.outFamily0(iolw.outfunction,maxFamily,Aval,iolw.throughput)
      }
      console.log("outFamily: ", _.map(outFamily, pltk.plprintset), outFamily)
      let result = iolw.netOutput(outFamily)
      console.log("netOutput: ", pltk.plprintset(result), result)
      return result
    } else {
      let result = iolw.outfunction(Aval,Nval, iolw.throughput)
      console.log("output: ", pltk.plprintset(result), result)
      return result
    }
  }
  
  $("#outputButton").click(function(){
    $("#output").removeClass("is-invalid")
    const output = calculateOutput()
    const resultText = pltk.plprintset(output)
    $("#output").val("Cn(".concat(resultText,")"))
  });
  
  const negativeAnswer = function(x) { return "No, the formula " + pltk.plprint(x) + " is not in the output set." }
  const positiveAnswer = function(x) { return "Yes, the formula " + pltk.plprint(x) + " is in the output set." }
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
        $('#response-text').text(positiveAnswer(xval))
      } else {
        $('#response').addClass("alert-warning")
        $('#response-text').text(negativeAnswer(xval))
      }
      $('#response').css('visibility', 'visible');
      window.setTimeout(function() {$('#response').css('visibility', 'collapse');}, 5000);
    }
  });
});

