
const express = require('express');
const bodyParser = require('body-parser');
const { exec } = require('child_process');
const fs = require('fs').promises;
const path = require('path');
const cors = require('cors');

const app = express();
// Extended payload size for larger code snippets
app.use(bodyParser.json({limit: '50mb'}));
app.use(bodyParser.text({limit: '50mb'}));
app.use(cors());

// Define API directory paths
const API_DIR = path.join(__dirname);
const INPUT_FILE = path.join(API_DIR, 'input.c');
const CODE_CPP = path.join(API_DIR, 'code.cpp');
const EXECUTABLE = path.join(API_DIR, 'converter');

// Get the content of input.c file
app.get('/api/input', async (req, res) => {
  try {
    const content = await fs.readFile(INPUT_FILE, 'utf8');
    res.send(content);
  } catch (error) {
    console.error('Error reading input file:', error);
    res.status(404).json({ error: 'Input file not found' });
  }
});

// Save content to input.c file
app.post('/api/save-input', async (req, res) => {
  try {
    await fs.writeFile(INPUT_FILE, req.body);
    console.log('Input code saved to:', INPUT_FILE);
    res.status(200).json({ message: 'Input code saved successfully' });
  } catch (error) {
    console.error('Error saving input file:', error);
    res.status(500).json({ error: 'Failed to save input file', details: error.message });
  }
});

// Convert C to Promela
app.post('/api/convert', async (req, res) => {
  try {
    const { code, model } = req.body;
    if (!code) {
      return res.status(400).json({ error: 'No code provided' });
    }

    const modelNum = model ? model.slice(-1) : '1';
    
    // Write input code to file
    const outputPath = path.join(API_DIR, `output${modelNum}.pml`);

    await fs.writeFile(INPUT_FILE, code);
    console.log('Input code written to file:', INPUT_FILE);

    // Write code.cpp file if it doesn't exist
    let codeIsAvailable = false;
    try {
      await fs.access(CODE_CPP);
      codeIsAvailable = true;
    } catch {
      codeIsAvailable = false;
    }
    
    if (!codeIsAvailable) {
      try {
        const codeContent = await fs.readFile(path.join(API_DIR, 'code.cpp'), 'utf-8');
        await fs.writeFile(CODE_CPP, codeContent);
        console.log('C++ converter code found at:', CODE_CPP);
      } catch (error) {
        console.error('Error with C++ code:', error);
        return res.status(500).json({ error: 'Failed to access C++ converter code', details: error.message });
      }
    }

    // Compile the C++ code
    console.log('Compiling C++ code...');
    const compileCommand = `g++ -o ${EXECUTABLE} ${CODE_CPP}`;
    
    exec(compileCommand, async (compileError, stdout, stderr) => {
      if (compileError) {
        console.error('Compilation error:', compileError);
        console.error('Stderr:', stderr);
        return res.status(500).json({ error: 'Failed to compile the converter', details: stderr });
      }

      console.log('Compilation successful. Running converter...');
      
      // Run the converter
      exec(`${EXECUTABLE} ${INPUT_FILE} ${outputPath}`, async (execError, execStdout, execStderr) => {
        if (execError) {
          console.error('Execution error:', execError);
          console.error('Stderr:', execStderr);
          return res.status(500).json({ 
            error: 'Failed to execute the converter',
            details: execStderr,
            command: `${EXECUTABLE} ${INPUT_FILE} ${outputPath}`
          });
        }

        try {
          // Read the output file
          console.log('Reading output file:', outputPath);
          const output = await fs.readFile(outputPath, 'utf8');
          res.json({ output });
        } catch (readError) {
          console.error('Read error:', readError);
          res.status(500).json({ error: 'Failed to read output file', details: readError.message });
        }
      });
    });
  } catch (error) {
    console.error('Server error:', error);
    res.status(500).json({ error: 'Server error', details: error.message });
  }
});

const PORT = process.env.PORT || 3001;
app.listen(PORT, () => {
  console.log(`Server running on port ${PORT}`);
});
