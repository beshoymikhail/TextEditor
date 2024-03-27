using TextEditor.Model;

namespace TextEditor.Services
{
    public static class HelperMethods
    {
        public static List<string> GetTabList(DocumentationType DocumentationType)
        {
            if (DocumentationType == DocumentationType.DataTypes)
            {
                return new List<string> { "Implementaion", "Specification" };
            }
            if (DocumentationType == DocumentationType.MainFunctions || DocumentationType == DocumentationType.SupportFunctions)
            {
                return new List<string> { "Functions", "Defined by" };
            }
            return new List<string>();
        }
        public static List<StructureType> GetStructureType(DocumentationType DocumentationType, string Panel)
        {
            if (DocumentationType == DocumentationType.DataTypes)
            {
                return new List<StructureType>
                {
                    StructureType.Inductive, StructureType.Record, StructureType.Definition, StructureType.Class
                };
            }
            else if ((DocumentationType == DocumentationType.MainFunctions || DocumentationType == DocumentationType.SupportFunctions) && Panel == "Functions")
            {
                return new List<StructureType>
                {
                    StructureType.Inductive, StructureType.Definition,StructureType.Fixpoint, StructureType.Function, StructureType.ProgramDefinition, StructureType.ProgramFixpoint
                };
            }
            else if ((DocumentationType == DocumentationType.MainFunctions || DocumentationType == DocumentationType.SupportFunctions) && Panel == "Defined by")
            {
                return new List<StructureType>
                {
                    StructureType.Lemma, StructureType.Theorem,StructureType.Fact, StructureType.Remark, StructureType.Corollary, StructureType.Proposition,StructureType.Property
                };
            }
            return new List<StructureType>();
        }
        public static List<SourceFile> GetSourceFiles(DocumentationType DocumentationType, string Panel)
        {
            if (DocumentationType == DocumentationType.DataTypes && Panel == "Implementaion")
            {
                return new List<SourceFile> { SourceFile.Implementation };
            }
            else if (DocumentationType == DocumentationType.DataTypes && Panel == "Specification")
            {
                return new List<SourceFile> { SourceFile.Specification };
            }
            else if ((DocumentationType == DocumentationType.MainFunctions || DocumentationType == DocumentationType.SupportFunctions) && Panel == "Functions")
            {
                return new List<SourceFile> { SourceFile.Implementation };
            }
            else if ((DocumentationType == DocumentationType.MainFunctions || DocumentationType == DocumentationType.SupportFunctions) && Panel == "Defined by")
            {
                return new List<SourceFile> { SourceFile.Auxiliary, SourceFile.Implementation, SourceFile.Specification };
            }
            return new List<SourceFile>();
        }
    }
}
