(() => {
  const { format } = require("./format");
  const fs = require("fs");
  const stdinBuffer = fs.readFileSync(0); // STDIN_FILENO = 0
  console.log(format(stdinBuffer.toString()));
})();
