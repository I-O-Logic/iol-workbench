iol = new function() { const lib = this;
  lib.out1 = function(A,N,x) {
    let N2 = N.filter(n => pltk.consequence(A, n[0]))
    let M = N2.map(n => n[1])
    return pltk.consequence(M, x)
  }
  
  lib.out1set = function(A,N) {
    //console.log("out1setN", N)
    let N2 = N.filter(n => pltk.consequence(A, n[0]))
    //console.log("out1setN2")
    let M = N2.map(n => n[1])
    return canonizeOut(M)
  }
  
  lib.out2 = function(A,N,x) {
    let dnf = pltk.dnf(pltk.mkConjs(A))
    let A2 = pltk.disjs(dnf)
    return A2.every(y => lib.out1([y],N,x))
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
      
      NN = _.uniqWith(_.flatMap(NNNotC,lib.subsetsOneSmaller), _.isEqual)
      console.log("subsets of NN", NN)
      NN = _.filter(NN, function(n) {return !_.some(result, r => lib.subset(n,r))})
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
  
  
  
  lib.subset = function(a,b) {
    return _.difference(a, b).length === 0
  }
  
  lib.subsetsOneSmaller = function(S) {
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


$(document).ready(function() {
  $("#output").on("keyup", function(event) {
    $("#output").removeClass("is-invalid")
  });

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
      console.log("here", Ctext)
      Cval = Ctext.split(',').map(plparse.read)
      console.log("here", Cval)
    }
    let result = iol.out1set(Aval,Nval)
    console.log("result", result, pltk.plprintset(result))
    let resultText = pltk.plprintset(result)
    $("#output").val("Cn(".concat(resultText,")"))
    console.log("cval", pltk.plprintset(Cval))
    let result2 = iol.maxFamily(iol.out1set, Nval, Aval, Cval)
    console.log("result2", result2)
    let result3 = iol.outFamily0(iol.out1set, result2, Aval)
    console.log("result3", result3)
    let result4 = _.intersectionWith(...result3, _.isEqual)
    console.log("result4", result4, pltk.plprintset(result4))
  });
  
  $("#checkButton").click(function(){
    $('#feedbackno').hide()
    $('#feedbackyes').hide()

    const Atext = $("#input").val()
    const Ntext = $("#norms").val()
    const Ctext = $('#constraints').val()
    const xtext = $("#output").val()
    
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
    const xval = plparse.read(xtext)
    if (xval == null) {
      $('#output').addClass("is-invalid")
      return
    }
   
    let out = null
    if ($('#out1r').prop("checked")) {
      out = iol.out1
    } else if ($('#out2r').prop("checked")) {
      out = iol.out2
    } else if ($('#out3r').prop("checked")) {
      out = iol.out3
    } else if ($('#out4r').prop("checked")) {
      out = iol.out4
    }
    let result = out(Aval,Nval,xval)
    if (result != null) {
      if (result) {
        $('#feedbackyes').show()
        window.setTimeout(function() {$('#feedbackyes').hide()}, 5000);
      } else {
        $('#feedbackno').show()
        window.setTimeout(function() {$('#feedbackno').hide()}, 5000);
      }
    }
  });
  
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
});

