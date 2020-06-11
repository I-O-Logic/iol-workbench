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

plparse = new function () { var lib = this;

  const binops = ['&','|'];
  const unaryops = ['~']; 
  const ops = binops.concat(unaryops)

  lib.read = function(input) {
    var ts = lib.lex(input)
    return lib.parse(ts)
  }

  lib.lex = function(input) {
    var acc = []
    var result = []
    input.split('').forEach(function(c) {
      if (c == '(') {
        if (acc.length > 0) {result.push({ type: 'VAR', content: acc.join('') }); acc = []; }
        result.push({ type: 'LP'})
      } else if (c == ')') {
        if (acc.length > 0) {result.push({ type: 'VAR', content: acc.join('') }); acc = []; }
        result.push({ type: 'RP'})
      } else if (ops.includes(c)) {
        if (acc.length > 0) {result.push({ type: 'VAR', content: acc.join('') }); acc = []; }
        result.push({ type: 'OP', content: c})
      } else if (c.trim() === '') {
        if (acc.length > 0) {result.push({ type: 'VAR', content: acc.join('') }); acc = []; }
      } else {
        acc.push(c)
      }
    })
    if (acc.length > 0) {result.push({ type: 'VAR', content: acc.join('') }); acc = []; }
    return result
  }
  
  lib.parse = function(ts) {
    var cur = 0
    var peek = function() {return ts[cur]}
    var consume = function() {return ts[cur++]}
    
    
    
    var parseAtomic = function() {
      if (!peek()) throw new Error("ParseError: Empty input for atomic")
      if (peek().type == 'VAR') {
        var variable = consume().content
        if (variable == "T") {
          return {op: 'LT', args: []}
        } else if (variable == "F") {
          return {op: 'LF', args: []}
        } else {
          return {op: 'Var', args: [variable]}
        }
      } else {
        throw new Error("ParseError: No atomic where atomic was expected: " + peek().content)
      }
    }
    
    var parseUnary = function() {
      if (!peek()) throw new Error("ParseError: Empty input for unary")
      if (peek().type == 'OP' && peek().content == '~') {
        var node = {op: consume().content, args: []}
        node.args.push(parseUnitary())
        return node
      } else {
        throw new Error("ParseError: No unary where unary was expected.")
      }
    }
    
    var parseUnitary = function() {
      if (!peek()) throw new Error("ParseError: Empty input for unitary")
      if (peek().type == 'LP') {
        consume()
        var node = parseFormula()
        if (peek().type == 'RP') {
          consume()
          return node
        } else {
          throw new Error("ParseError: Unbalanced parentheses in unitary formula")
        }
      }
      if (peek().type == 'VAR') {
        return parseAtomic()
      }
      if (peek().type == 'OP') {
        return parseUnary()
      }
      throw new Error("ParseError: Unexpected input for unitary formula: " + peek().content)
    }
    
    var parseBinary = function(left) {
      if (!peek()) throw new Error("ParseError: Empty input for binary")
      if (peek().type == 'OP' && binops.includes(peek().content)) {
        var node = {op: consume().content, args: [left]}
        node.args.push(parseUnitary())
        return node
      } else {
        throw new Error("ParseError: No binary where binary was expected.")
      }
    }
    
    var parseFormula = function() {
      if (!!peek()) {
        var node = null
        while (!!peek()) {
          if (node != null) {
            // sth already parsed
            if (peek().type == 'OP') {
              if (binops.includes(peek().content)) {
                // binary op
                /*if (binops.includes(node.op)) {
                  // already parsed binary op, then it must be same
                  if (node.op == peek().content) {
                    // todo: parse binary
                    node = parseBinary(node)
                  } else {
                    throw new Error("ParseError: Mixed binary operators")
                  }
                } else*/ {
                  // todo: parse binary
                  node = parseBinary(node)
                }
              } else {
                // unary op, error
                throw new Error("ParseError: Unary operator where binary operator expected")
              }
            } else return node
          } else {
            // nothing parsed yet
            // can be either binary or unitary
            if (peek().type == 'LP') {
              node = parseUnitary()
            } else if (peek().type == 'OP') {
              // can only be negation
              node = parseUnary()
            } else if (peek().type == 'VAR') {
              node = parseAtomic()
            }
          }
        }  
        return node
      } else {
        return null
      }
    }

    var result = parseFormula()
    if (!!peek()) { throw new Error("ParseError: Unconsumed input.") }
    return result
  }
  
}
