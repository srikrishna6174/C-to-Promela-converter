import { useNavigate } from 'react-router-dom';
import { Button } from '@/components/ui/button';
import { Card } from '@/components/ui/card';
import Navbar from '@/components/Navbar';

const Home = () => {
  const navigate = useNavigate();

  const models = [
    {
      id: 1,
      title: "Model 1",
      description: "Parses C code with regex‑based detectors and a context stack to identify types, functions, and control flow. Generates corresponding Promela typedefs, proctypes, channels, loops, and heap models to mirror the original C behavior",
    },
    {
      id: 2,
      title: "Model 2",
      description: "Parses the C source into an AST using pycparser and collects types, structs, and functions. Traverses each AST node to emit equivalent Promela proctypes, memory pools, and control‐flow constructs.",
    }
  ];

  return (
    <div className="min-h-screen bg-background transition-colors duration-300">
      <Navbar />
      <div className="container mx-auto px-4 py-12">
        <div className="text-center mb-16">
          <h1 className="text-4xl font-bold mb-4 text-foreground">
            C to Promela Code Converter
          </h1>
          <p className="text-xl text-foreground/80 max-w-2xl mx-auto">
            Transform your C code into Promela models for formal verification using our state-of-the-art conversion models.
          </p>
        </div>

        <div className="flex flex-col md:flex-row gap-8">
          {models.map((model) => (
            <Card key={model.id} className="flex-1 p-6 rounded-xl shadow-lg">
              <h2 className="text-3xl font-semibold text-foreground mb-4">
                {model.title}
              </h2>
              <p className="text-foreground/80 text-lg mb-6">
                {model.description}
              </p>
              <Button
                onClick={() => navigate(`/converter?model=${model.id}`)}
                className="group bg-primary text-white hover:bg-primary/90 rounded-full"
              >
                Try Model {model.id}
              </Button>
            </Card>
          ))}
        </div>
      </div>
    </div>
  );
};

export default Home;
