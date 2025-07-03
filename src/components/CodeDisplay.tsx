
import { Card } from "@/components/ui/card";
import { useEffect, useState } from "react";

interface CodeDisplayProps {
  title: string;
  code: string;
}

const CodeDisplay = ({ title, code }: CodeDisplayProps) => {
  const [isDarkTheme, setIsDarkTheme] = useState(false);

  useEffect(() => {
    const currentTheme = document.documentElement.getAttribute('data-theme') || 'light';
    setIsDarkTheme(currentTheme === 'dark');

    const observer = new MutationObserver((mutations) => {
      mutations.forEach((mutation) => {
        if (mutation.attributeName === 'data-theme') {
          const newTheme = document.documentElement.getAttribute('data-theme') || 'light';
          setIsDarkTheme(newTheme === 'dark');
        }
      });
    });
    
    observer.observe(document.documentElement, { attributes: true });
    
    return () => observer.disconnect();
  }, []);

  return (
    <Card className={`p-4 ${isDarkTheme ? 'bg-secondary' : 'bg-accent/10'} border border-accent/20 rounded-xl shadow-md`}>
      <h2 className={`text-lg font-semibold mb-2 ${isDarkTheme ? 'text-white' : 'text-[#543310]'}`}>{title}</h2>
      <pre className={`${isDarkTheme ? 'bg-accent/10' : 'bg-primary/10'} p-4 rounded-lg overflow-x-auto`}>
        <code className={`text-sm font-mono ${isDarkTheme ? 'text-white' : 'text-[#543310]'}`}>{code}</code>
      </pre>
    </Card>
  );
};

export default CodeDisplay;
