
import { useState, useEffect } from 'react';
import { Textarea } from "@/components/ui/textarea";
import { Card } from "@/components/ui/card";

interface CodeEditorProps {
  value: string;
  onChange: (value: string) => void;
  language?: string;
}

const CodeEditor = ({ value, onChange, language = 'javascript' }: CodeEditorProps) => {
  const [focused, setFocused] = useState(false);
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
    <Card className={`p-4 ${isDarkTheme ? 'bg-secondary' : 'bg-accent/10'} border border-accent/20 rounded-xl shadow-md transition-all duration-200 h-full ${focused ? 'ring-2 ring-primary/50' : ''}`}>
      <Textarea
        value={value}
        onChange={(e) => onChange(e.target.value)}
        className={`w-full h-full min-h-[300px] font-mono text-sm ${isDarkTheme ? 'bg-accent/10 text-white' : 'bg-primary/10 text-[#543310]'} border-none focus-visible:ring-0 resize-none rounded-lg`}
        onFocus={() => setFocused(true)}
        onBlur={() => setFocused(false)}
        placeholder={`// Enter your ${language} code here...`}
        spellCheck="false"
      />
    </Card>
  );
};

export default CodeEditor;
