using TextEditor.Model;

namespace TextEditor.Services
{
    public static class HelperMethods
    {
        public static List<string> GetTabList(SectionType sectionType)
        {
            if (sectionType == SectionType.DataTypes)
            {
                return new List<string> { "Implementaion", "Specification" };
            }
            if (sectionType == SectionType.MainFunctions || sectionType == SectionType.SupportFunctions)
            {
                return new List<string> { "Functions", "Defined by" };
            }
            return new List<string>();
        }
        public static List<FunctionType> GetFunctionType(SectionType sectionType, string Panel)
        {
            if (sectionType == SectionType.DataTypes)
            {
                return new List<FunctionType>
                {
                    FunctionType.Inductive, FunctionType.Record, FunctionType.Definition, FunctionType.Class
                };
            }
            else if ((sectionType == SectionType.MainFunctions || sectionType == SectionType.SupportFunctions) && Panel == "Functions")
            {
                return new List<FunctionType>
                {
                    FunctionType.Inductive, FunctionType.Definition,FunctionType.Fixpoint, FunctionType.Function, FunctionType.ProgramDefinition, FunctionType.ProgramFixpoint
                };
            }
            else if ((sectionType == SectionType.MainFunctions || sectionType == SectionType.SupportFunctions) && Panel == "Defined by")
            {
                return new List<FunctionType>
                {
                    FunctionType.Lemma, FunctionType.Theorems,FunctionType.Fact, FunctionType.Remark, FunctionType.Corollary, FunctionType.Proposition,FunctionType.Properties
                };
            }
            return new List<FunctionType>();
        }
        public static List<SourceFile> GetSourceFiles(SectionType sectionType, string Panel)
        {
            if (sectionType == SectionType.DataTypes && Panel == "Implementaion")
            {
                return new List<SourceFile> { SourceFile.Implementation };
            }
            else if (sectionType == SectionType.DataTypes && Panel == "Specification")
            {
                return new List<SourceFile> { SourceFile.Specification };
            }
            else if ((sectionType == SectionType.MainFunctions || sectionType == SectionType.SupportFunctions) && Panel == "Functions")
            {
                return new List<SourceFile> { SourceFile.Implementation };
            }
            else if ((sectionType == SectionType.MainFunctions || sectionType == SectionType.SupportFunctions) && Panel == "Defined by")
            {
                return new List<SourceFile> { SourceFile.Auxiliary, SourceFile.Implementation, SourceFile.Specification };
            }
            return new List<SourceFile>();
        }
    }
}
