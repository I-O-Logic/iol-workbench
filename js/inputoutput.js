iol = new function() { const lib = this;
  lib.out1 = function(A,N,x) {
    let N2 = N.filter(n => pltk.consequence(A, n[0]))
    let M = N2.map(n => n[1])
    return pltk.consequence(M, x)
  }
  
  lib.out1set = function(A,N) {
    let N2 = N.filter(n => pltk.consequence(A, n[0]))
    let M = N2.map(n => n[1])
    console.log(pltk.plprintset(M))
    let Msimp = pltk.simpset(M)
    console.log(pltk.plprintset(Msimp))
    let together = pltk.mkConjs(Msimp)
    console.log(pltk.plprint(together))
    let cnf = pltk.cnf(together)
    console.log(cnf,pltk.plprint(cnf))
    let cnfSimp = pltk.cnfsimp(cnf)
    console.log(cnfSimp, pltk.plprint(cnfSimp))
    let result = pltk.conjs(cnfSimp)
    return result
  }
  
  let canonizeOut = function(N) {
    let Msimp = pltk.simpset(M)
    console.log(pltk.plprintset(Msimp))
    let together = pltk.mkConjs(Msimp)
    console.log(pltk.plprint(together))
    let cnf = pltk.cnf(together)
    console.log(cnf,pltk.plprint(cnf))
    let cnfSimp = pltk.cnfsimp(cnf)
    console.log(cnfSimp, pltk.plprint(cnfSimp))
    let result = pltk.conjs(cnfSimp)
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
  
  lib.outFamily = function(out,N,A,C,x) {
    let NN = [N]
    let result = []
    
    while (!(_.isEmpty(NN))) {
      const n = _.size(_.sample(NN))
      NNC = _.filter(NN, function(x) { /* todo */ })
      result = _.concat(result, NNC)
      NNNotC = _.without(NN,NNC)
      
      NN = _.uniqWith(_.flatMap(NN,self.subsetsOneSmaller), _.isEqual)
      NN = _.filter(NN, function(n) {!_.includes(result,n)})
    }
  }
  
  lib.subsetsOneSmaller = function(S) {
    let result = []
    S.forEach(s => 
      result.push(_.without(S,s))
    )
    return result
  }
}

    $(document).ready(function() {
        $("#output").on("keyup", function(event) {
          $("#output").removeClass("is-invalid")
        })
        $("#outputButton").click(function(){
          const Atext = $("#input").val()
          const Ntext = $("#norms").val()
          let Aval = []
          if (Atext.length > 0) {
            Aval = Atext.split(',').map(plparse.read)
          }
          let Nval = []
          if (Ntext.length > 0) {
            Nval = Ntext.trim().split('\n').filter(y => y.length > 0).map(x => x.trim().slice(1,-1).split(',').map(plparse.read))
          }
          let result = iol.out1set(Aval,Nval)
          console.log("result", pltk.plprintset(result))
          let resultText = pltk.plprintset(result)
          $("#output").val("Cn(".concat(resultText,")"))
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
