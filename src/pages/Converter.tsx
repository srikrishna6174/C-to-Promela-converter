
import { useState, useEffect } from 'react';
import { useNavigate, useLocation } from 'react-router-dom';
import { toast } from 'sonner';
import Navbar from '@/components/Navbar';
import CodeEditor from '@/components/CodeEditor';
import CodeDisplay from '@/components/CodeDisplay';
import { Button } from '@/components/ui/button';
import { Loader2 } from 'lucide-react';
import inputCFile from '@/codes/input.c?raw';
import output1File from '@/codes/output1.pml?raw';
import output2File from '@/codes/output2.pml?raw';

const Converter = () => {
  const [inputCode, setInputCode] = useState('');
  const [outputCode, setOutputCode] = useState('');
  const [isLoading, setIsLoading] = useState(false);
  const [currentModel, setCurrentModel] = useState('model1');
  const navigate = useNavigate();
  const location = useLocation();

  useEffect(() => {
    const modelFromUrl = new URLSearchParams(location.search).get('model');
    if (modelFromUrl) {
      setCurrentModel(`model${modelFromUrl}`);
    }

    // Load initial input code from static file
    setInputCode(inputCFile);

    // Load the correct output based on model
    if (currentModel === 'model1') {
      setOutputCode(output1File);
    } else if (currentModel === 'model2') {
      setOutputCode(output2File);
    }
  }, [location.search]);

  // Update output when model changes
  useEffect(() => {
    if (currentModel === 'model1') {
      setOutputCode(output1File);
    } else if (currentModel === 'model2') {
      setOutputCode(output2File);
    }
  }, [currentModel]);

  const handleModelChange = (model: string) => {
    setCurrentModel(model);
  };

  const handleConvert = async () => {
    setIsLoading(true);
    
    try {
      // Simulate conversion process
      setTimeout(() => {
        if (currentModel === 'model1') {
          setOutputCode(output1File);
          toast.success('Code converted using Model 1');
        } else if (currentModel === 'model2') {
          setOutputCode(output2File);
          toast.success('Code converted using Model 2');
        }
        setIsLoading(false);
      }, 1000);
    } catch (error) {
      console.error('Error converting code:', error);
      toast.error(`Failed to convert code: ${error instanceof Error ? error.message : 'Unknown error'}`);
      setOutputCode('// Error converting code. Please try again.');
      setIsLoading(false);
    }
  };

  return (
    <div className="min-h-screen bg-background transition-colors duration-300">
      <Navbar onModelChange={handleModelChange} />
      <main className="container mx-auto py-8 px-4">
        <h1 className="text-3xl font-bold text-center mb-8 text-foreground">
          C to Promela Code Converter
        </h1>
        
        <div className="grid grid-cols-1 md:grid-cols-2 gap-8">
          <div className="flex flex-col space-y-4">
            <h2 className="text-xl font-semibold text-foreground">Input C Code</h2>
            <div className="h-96">
              <CodeEditor 
                value={inputCode} 
                onChange={setInputCode} 
                language="c" 
              />
            </div>
            
          </div>
          
          <div className="flex flex-col space-y-4">
            <h2 className="text-xl font-semibold text-foreground">Generated Promela Code</h2>
            <CodeDisplay 
              title={`Output (${currentModel.charAt(0).toUpperCase() + currentModel.slice(1)})`}
              code={outputCode || '// Converted code will appear here...'}
            />
          </div>
        </div>

        <div className="mt-12 bg-accent/5 p-6 rounded-xl border border-accent/20">
  <h3 className="text-xl font-semibold mb-4 text-foreground">How to Run the C to Promela Converter</h3>
  
  <ol className="list-decimal pl-5 space-y-3 text-foreground">
    
    <li>
      <strong>Open Terminal 1</strong> and navigate to the <code className="bg-primary/10 px-2 py-1 rounded text-primary">code-view-converter</code> directory.
    </li>
    <li>
      <strong>Run the web server</strong> using <code className="bg-primary/10 px-2 py-1 rounded text-primary">npm install, npm run dev</code>.
    </li>
    <li>
      <strong>Open Terminal 2</strong> and navigate to <code className="bg-primary/10 px-2 py-1 rounded text-primary">code-view-converter/src/codes/</code>.
    </li>
    <li>
      <strong>Compile and execute the converter logic</strong> with:
      <code className="block bg-primary/10 px-2 py-1 rounded text-primary mt-1">
        g++ code1.cpp -o code1 && ./code1 && python3 code2.py input.c -o output2.pml
      </code>
    </li>
    <li>
      <strong>Open your browser</strong> and go to <code className="bg-primary/10 px-2 py-1 rounded text-primary">http://localhost:3000</code> to view the code conversion in both models.
    </li>
    <li>if unable to run above, go to src/codes and run cpp, py using "g++ code1.cpp -o code1 && ./code1 && python3 code2.py input.c -o output2.pml", view output in output1.pml and output2.pml</li>
    
  </ol>
</div>

      </main>
    </div>
  );
};

export default Converter;
