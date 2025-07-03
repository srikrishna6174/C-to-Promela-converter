
import { useState, useEffect } from 'react';
import { useParams } from 'react-router-dom';
import Navbar from '@/components/Navbar';
import CodeDisplay from '@/components/CodeDisplay';

const Index = () => {
  const [inputCode, setInputCode] = useState('');
  const [outputCode, setOutputCode] = useState('');
  const [currentModel, setCurrentModel] = useState('model1');
  const { id } = useParams();

  useEffect(() => {
    if (id) {
      setCurrentModel(`model${id}`);
    }

    // Load input code
    fetch('/src/codes/input.c')
      .then(response => response.text())
      .then(text => setInputCode(text))
      .catch(error => console.error('Error loading input code:', error));

    // Load output code based on model
    const modelNumber = id || '1';
    loadOutputCode(`model${modelNumber}`);
  }, [id]);

  const loadOutputCode = (model: string) => {
    fetch(`/src/codes/output${model.slice(-1)}.pml`)
      .then(response => response.text())
      .then(text => setOutputCode(text))
      .catch(error => console.error('Error loading output code:', error));
  };

  const handleModelChange = (model: string) => {
    setCurrentModel(model);
    loadOutputCode(model);
  };

  return (
    <div className="min-h-screen bg-background transition-colors duration-300">
      <Navbar onModelChange={handleModelChange} />
      <main className="container mx-auto py-8 px-4">
        <h1 className="text-3xl font-bold text-center mb-8 text-foreground">
          C to Promela Code Converter
        </h1>
        <div className="grid grid-cols-1 md:grid-cols-2 gap-8">
          <div className="flex flex-col space-y-4 transition-all duration-300 ease-in-out">
            <CodeDisplay title="Input C Code" code={inputCode} />
          </div>
          <div className="flex flex-col space-y-4 transition-all duration-300 ease-in-out">
            <CodeDisplay 
              title={`Output (${currentModel.charAt(0).toUpperCase() + currentModel.slice(1)})`} 
              code={outputCode} 
            />
          </div>
        </div>
      </main>
    </div>
  );
};

export default Index;
