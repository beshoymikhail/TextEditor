namespace TextEditor.Model
{
    public class Structure
    {
        public int Id { get; set; }
        public string Name { get; set; }
        public string Description { get; set; }
        public StructureType StructureType { get; set; }
        public SourceFile sourceFile { get; set; }
    }
  
}
