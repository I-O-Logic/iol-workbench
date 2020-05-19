iol = new function() { const lib = this;
  lib.out1 = function(A,N,x) {
    let N2 = N.filter(n => pltk.consequence(A, n[0]))
    let M = N2.map(n => n[1])
    return pltk.consequence(M, x)
  }
  
  lib.out1set = function(A,N) {
    let N2 = N.filter(n => pltk.consequence(A, n[0]))
    let M = N2.map(n => n[1])
    return canonizeOut(M)
  }
  
  lib.out2 = function(A,N,x) {
    let dnf = pltk.dnf(pltk.mkConjs(A))
    let A2 = pltk.disjs(dnf)
    return A2.every(y => lib.out1([y],N,x))
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
  
  lib.out3 = function(A,N,x) {
    let A2 = A.slice()
    let N2 = N.filter(n => pltk.consequence(A2, n[0]))
    let NN = N.filter(n => !N2.includes(n))
    while (!pltk.consequence(N2.map(n => n[1]),x)) {
      A2 = A2.concat(N2.map(n => n[1]))
      let M = NN.filter(n => pltk.consequence(A2, n[0]))
      if (M.length == 0) {
        return false
      } else {
        N2 = N2.concat(M)
        NN = NN.filter(n => !M.includes(n))
      }
    }
    return true
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
  
  lib.out4 = function(A,N,x) {
    let dnf = pltk.dnf(pltk.mkConjs(A))
    let A2 = pltk.disjs(dnf)
    return A2.every(function(y) {
      let A3 = [y]
      let N2 = N.filter(n => pltk.consequence(A3, n[0]))
      let NN = N.filter(n => !N2.includes(n))
      if (!pltk.consequence(N2.map(n => n[1]),x)) {
        A3 = A3.concat(N2.map(n => n[1]))
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
  }
  
  lib.maxFamily = function(out,N,A,C) {
    let NN = [N]
    let result = []
    
    console.log("N", N)
    console.log("NN", NN)
    console.log("A", A)
    console.log("C", C)
       
    while (!(_.isEmpty(NN))) {
      console.log("####")
      const n0 = _.size(_.sample(NN))
      console.log("n0", n0)
      console.log("NN[0]", NN[0])
      NNC = _.filter(NN, function(x) {
        console.log("x", x)
        return pltk.consistent(out(A,x).concat(C))
      })
      console.log("NNC", NNC)
      result = _.concat(result, NNC)
      NNNotC = _.without(NN,NNC)
      console.log("NNNotC", NNNotC)
      
      NN = _.uniqWith(_.flatMap(NNNotC,subsetsOneSmaller), _.isEqual)
      console.log("subsets of NN", NN)
      NN = _.filter(NN, function(n) {return !_.some(result, r => subset(n,r))})
      console.log("NN", NN)
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
}

outfunction = iol.out1
throughput = false
constraints = false
netOutput = null
preference = null
const negativeAnswer = "No, the formula x is not in the output set."
const positiveAnswer = "Yes, the formula x is in the output set."


$(document).ready(function() {
  // Examples
  $("#example1button").click(function(){
    $("#output").removeClass("is-invalid")
    $("#input").val('a,b')
    //$("#norms").val('(a,x)\n(b,y)')
    $("#norms").val('(a,x)\n(b,(x | y) & (x | ~y))')
    $("#constraints").val('c')
    $("#output").val('x & y')
  });
  $("#example2button").click(function(){
    $("#output").removeClass("is-invalid")
    $("#input").val('a|b')
    $("#norms").val('(a,x)\n(b,x)')
    $("#output").val('x')
  });
  $("#example3button").click(function(){
    $("#output").removeClass("is-invalid")
    $("#input").val('a,b')
    $("#norms").val('(a,x)\n(b,y)\n(a&b,z)')
    $("#output").val('z')
  });

  // Parse error handling
  $("#input").on("keyup", function(event) {
    $("#input").removeClass("is-invalid")
  });
  $("#norms").on("keyup", function(event) {
    $("#norms").removeClass("is-invalid")
  });
  $("#constraints").on("keyup", function(event) {
    $("#constraints").removeClass("is-invalid")
  });
  $("#output").on("keyup", function(event) {
    $("#output").removeClass("is-invalid")
  });
  
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
    } else {
      constraints = false
      $('#radio-net-credulous').prop("disabled", true);
      $('#radio-net-skeptical').prop("disabled", true);
      $('#constraints').prop("disabled", true);
    }
  });
  $('input[type=radio][name=io-constrained-net]').change(function() {
    netOutput = this.value
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
  
  // iol functionality
  $("#outputButton").click(function(){
    const Atext = $("#input").val()
    const Ntext = $("#norms").val()
    const Ctext = $('#constraints').val()
    
    let Aval = []
    if (Atext.length > 0) {
      Aval = Atext.split(',').map(plparse.read)
    }
    let Nval = []
    if (Ntext.length > 0) {
      Nval = Ntext.trim().split('\n').filter(y => y.length > 0).map(x => x.trim().slice(1,-1).split(',').map(plparse.read))
    }
    let Cval = []
    if (Ctext.length > 0) {
      Cval = Ctext.split(',').map(plparse.read)
    }
    
    let result = iol.out3set(Aval,Nval)
    console.log("result", result, pltk.plprintset(result))
    let resultText = pltk.plprintset(result)
    $("#output").val("Cn(".concat(resultText,")"))
    /*console.log("consequence:", pltk.consequence(result, xval))
    console.log("cval", pltk.plprintset(Cval))
    let result2 = iol.maxFamily(iol.out1set, Nval, Aval, Cval)
    console.log("result2", result2)
    let result3 = iol.outFamily0(iol.out1set, result2, Aval)
    console.log("result3", result3)
    let result4 = _.intersectionWith(...result3, _.isEqual)
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
    
    let result = outfunction(Aval,Nval,xval)
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

