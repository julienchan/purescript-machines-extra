var readline = require('readline');

exports.createReadline = function () {
  return readline.createInterface({
    input: process.stdin,
    output: process.stdout
  });
}

exports._askQuestion = function (nonCanceler, quest, rl) {
  return function (success, error) {
    rl.question(quest, function (answer) {
      success(answer)
    })
    return nonCanceler
  }
}

exports.closeReadline = function (rl) {
  return function () {
    return rl.close()
  }
}
