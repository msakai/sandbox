var Module = {
    noInitialRun : true,
    'print': function(text) {
        var element = document.getElementById('log');
        element.innerHTML += text.replace('\n', '<br>', 'g') + '<br>';
    }
};

function focusAndSelect(input) {
    input.focus();
    setTimeout(function(){ input.select(); }, 0)
}

var inputs;
var outputs;

function getInputString() {
    var result = "";
    for (var i = 0; i < 9; i++) {
        for (var j = 0; j < 9; j++) {
            var c = inputs[i][j].val();
            if (c.length == 1)
                result += c;
            else
                result += ".";
        }
    }
    return result;
}

function setInputString(str) {
    for (var i = 0; i < 9; i++) {
        for (var j = 0; j < 9; j++) {
            var c = str.charAt(i*9+j);
            if (c.match(/\d/))
                inputs[i][j].val(c)
            else
                inputs[i][j].val("")
        }
    }
}

function clearInput() {
    for (var i = 0; i < 9; i++) {
        for (var j = 0; j < 9; j++) {
            inputs[i][j].val("")
        }
    }
}

function renderOutput(inputStr, outputStr) {
    for (var i = 0; i < 9; i++) {
        for (var j = 0; j < 9; j++) {
            var e = outputs[i][j];
            e.text(outputStr.charAt(i*9+j));
            if (inputStr.charAt(i*9+j).match(/\d/)) {
                e.addClass("given");
            } else {
                e.removeClass("given");
            }
        }
    }
}

function clearOutput() {
    for (var i = 0; i < 9; i++) {
        for (var j = 0; j < 9; j++) {
            outputs[i][j].text("")
        }
    }
}

/*
var sampleInput = 
    "1..6..8.." +
    ".2..7..9." +
    "..3..8..1" +
    "2..4..9.." +
    ".3..5..1." +
    "..4..6..2" +
    "3..5..7.." +
    ".4..6..8." +
    "..5..7..4";
*/

// from <http://commons.wikimedia.org/wiki/File:Sudoku-by-L2G-20050714.svg>
var sampleInput = 
    "53..7...." +
    "6..195..." +
    ".98....6." +
    "8...6...3" +
    "4..8.3..1" +
    "7...2...6" +
    ".6....28." +
    "...419..5" +
    "....8..79";

$(document).ready(function(){
    inputs  = new Array(9);
    outputs = new Array(9);

    var rows = document.getElementById("input").getElementsByTagName("tr");
    for (var i = 0; i < 9; i++) {
        var xs = rows[i].getElementsByTagName("input");
        inputs[i] = new Array(9);
        for (var j = 0; j < 9; j++) {
            inputs[i][j] = $(xs[j]);
        }
    }

    var rows = document.getElementById("output").getElementsByTagName("tr");
    for (var i = 0; i < 9; i++) {
        var xs = rows[i].getElementsByTagName("td");
        outputs[i] = new Array(9);
        for (var j = 0; j < 9; j++) {
            outputs[i][j] = $(xs[j]);
        }
    }
    
    $("#solve").click(function() {
	sudoku = Module.cwrap('sudoku_c', 'string', ['string']);

	var input_str = getInputString();
	console.log(input_str)

	var output_str = sudoku(input_str);
	console.log(output_str);

	if (output_str != "") {
	    renderOutput(input_str, output_str);
	} else {
	    clearOutput();
	    alert("NO SOLUTION");
	}
    })


    $("#clear").click(function() {
	clearInput();
	clearOutput();
    })

    $("#load-sample").click(function() {
        setInputString(sampleInput)
    })

    function dumpToTextArea(str) {
        var s = ""
        for (var i = 0; i < 9; i++) {
            s += str.substr(i*9, 9) + "\n"
        }
        $("#textarea")[0].value = s
    }

    dumpToTextArea(sampleInput)

    $("#load-from-textarea").click(function() {
        setInputString($("#textarea")[0].value.replace(/#.*/g, '').replace(/\s+/g,''))
    })

    $("#save-to-textarea").click(function() {
        dumpToTextArea(getInputString())
    })

    for (var i = 0; i < 9; i++) {
        for (var j = 0; j < 9; j++) {
            (function(i,j) {
                inputs[i][j].click(function(){
                    focusAndSelect(inputs[i][j]);
                });

                inputs[i][j].keydown(function(e) {
                    // 37: ←
                    // 38: ↑
                    // 39: →
                    // 40: ↓
                    if (e.which==37 && 0 < j) {
                        focusAndSelect(inputs[i][j-1])
                    } else if (e.which==38 && 0 < i) {
                        focusAndSelect(inputs[i-1][j])
                    } else if (e.which==39 && j < 8) {
                        focusAndSelect(inputs[i][j+1])
                    } else if (e.which==40 && i < 8) {
                        focusAndSelect(inputs[i+1][j])
                    }
                })
            })(i,j)
        }
    }
});
