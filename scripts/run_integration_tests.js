const fs = require("fs");
const child_process = require("child_process");
const path = require("path");
const pjson = require("../package.json");

const exampleDirNames = ["deadcode"];
const exampleDirPaths = exampleDirNames.map((exampleName) =>
  path.join(__dirname, "..", "examples", exampleName)
);

const isWindows = /^win/i.test(process.platform);

const redderFile = path.join(__dirname, "../_build/default/src/Redder.exe");

/*
Needed for wrapping the stdout pipe with a promise
*/
function wrappedSpawn(command, args, options) {
  return new Promise((resolve, reject) => {
    const child = child_process.spawn(command, args, {
      env: process.env,
      ...options,
    });

    child.stdout.pipe(process.stdout);
    child.stderr.pipe(process.stderr);

    child.on("exit", (code) => {
      if (code == 0) {
        resolve(code);
      } else {
        reject(code);
      }
    });

    child.on("error", (err) => {
      console.error(`${command} ${args.join(" ")} exited with ${err.code}`);
      return reject(err.code);
    });
  });
}

async function installExamples() {
  const tasks = exampleDirPaths.map((cwd) => {
    console.log(`${cwd}: npm install --no-save (takes a while)`);

    // The npm command is not an executable, but a cmd script on Windows
    // Without the shell = true, Windows will not find the program and fail
    // with ENOENT
    const shell = isWindows ? true : false;
    return wrappedSpawn("npm", ["install", "--no-save"], {
      cwd,
      shell,
    });
  });

  return Promise.all(tasks);
}

function cleanBuildExamples() {
  for (let i = 0; i < exampleDirPaths.length; i++) {
    const cwd = exampleDirPaths[i];
    console.log(`${cwd}: npm run clean && npm run build (takes a while)`);

    const shell = isWindows ? true : false;
    child_process.execFileSync("npm", ["run", "clean"], {
      cwd,
      shell,
      stdio: [0, 1, 2],
    });
    child_process.execFileSync("npm", ["run", "build"], {
      cwd,
      shell,
      stdio: [0, 1, 2],
    });
    child_process.execFileSync("npm", ["run", "analyze"], {
      cwd,
      shell,
      stdio: [0, 1, 2],
    });
  }
}

function checkDiff() {
  exampleDirNames.forEach((example) => {
    const exampleDir = path.join(path.join("examples", example), "src");
    console.log(`Checking for changes in '${exampleDir}'`);

    const output = child_process.execFileSync(
      "git",
      ["diff", "--", exampleDir + "/"],
      {
        encoding: "utf8",
      }
    );

    if (output.length > 0) {
      throw new Error(
        `Changed files detected in path '${exampleDir}'! Make sure redder is emitting the right code and commit the files to git` +
          "\n" +
          output +
          "\n"
      );
    }
  });
}

function checkSetup() {
  console.log("Checking if --version outputs the right version");
  let output;

  /* Compare the --version output with the package.json version number (should match) */
  try {
    output = child_process.execSync(`${redderFile} --version`, {
      shell: isWindows,
      encoding: "utf8",
    });
  } catch (e) {
    throw new Error(
      `redder --version caused an unexpected error: ${e.message}`
    );
  }

  // For Unix / Windows
  const stripNewlines = (str = "") => str.replace(/[\n\r]+/g, "");

  if (output.indexOf(pjson.version) === -1) {
    throw new Error(
      path.basename(redderFile) +
        ` --version doesn't contain the version number of package.json` +
        `("${stripNewlines(output)}" should contain ${pjson.version})` +
        `- Run \`node scripts/bump_version_module.js\` and rebuild to sync version numbers`
    );
  }
}

async function main() {
  try {
    checkSetup();
    await installExamples();
    cleanBuildExamples();

    /* Git diffing is broken... we need a better way to test regressions */
    checkDiff();

    console.log("Test successful!");
  } catch (e) {
    console.error(`Test failed unexpectly: ${e.message}`);
    console.error(e);
    process.exit(1);
  }
}

main();
