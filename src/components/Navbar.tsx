
import { useState } from 'react';
import { Button } from "@/components/ui/button";
import ThemeToggle from "./ThemeToggle";
import { useNavigate, useLocation } from 'react-router-dom';

interface NavbarProps {
  onModelChange?: (model: string) => void;
}

const Navbar = ({ onModelChange }: NavbarProps) => {
  const [activeModel, setActiveModel] = useState('model1');
  const navigate = useNavigate();
  const location = useLocation();
  
  const isConverterPage = location.pathname === '/converter';
  const isHomePage = location.pathname === '/';
  const isModelPage = location.pathname.includes('/model/');

  const handleModelChange = (model: string) => {
    if (onModelChange) {
      setActiveModel(model);
      onModelChange(model);
    }
  };

  return (
    <nav className="bg-primary text-white p-4 shadow-lg rounded-b-lg">
      <div className="container mx-auto flex justify-between items-center">
        <div className="flex items-center gap-4">
          <h1 className="text-xl font-semibold cursor-pointer dark:text-white text-[#543310]" onClick={() => navigate('/')}>
            C to Promela
          </h1>
          <div className="space-x-2">
            <Button
              variant={isHomePage ? 'secondary' : 'ghost'}
              onClick={() => navigate('/')}
              className={`rounded-full ${
                isHomePage 
                  ? 'bg-secondary text-white' 
                  : 'dark:text-white text-[#543310] hover:bg-secondary/10'
              }`}
            >
              Home
            </Button>
            <Button
              variant={isConverterPage ? 'secondary' : 'ghost'}
              onClick={() => navigate('/converter')}
              className={`rounded-full ${
                isConverterPage 
                  ? 'bg-secondary text-white' 
                  : 'dark:text-white text-[#543310] hover:bg-secondary/10'
              }`}
            >
              Converter
            </Button>
          </div>
          
          {isConverterPage && (
            <div className="space-x-2 ml-4">
              {[1, 2].map((num) => (
                <Button
                  key={num}
                  variant={activeModel === `model${num}` ? 'secondary' : 'ghost'}
                  onClick={() => handleModelChange(`model${num}`)}
                  className={`rounded-full ${
                    activeModel === `model${num}`
                      ? 'bg-secondary text-white'
                      : 'dark:text-white text-[#543310] hover:bg-secondary/10'
                  }`}
                >
                  Model {num}
                </Button>
              ))}
            </div>
          )}
        </div>
        <ThemeToggle />
      </div>
    </nav>
  );
};

export default Navbar;
