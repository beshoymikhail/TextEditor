 namespace TextEditor.Model
{
    public enum FunctionType
    {
        Function,
        Lemma,
        Fixpoint,
    }
    public enum SourceFile
    {
        Implementation,
        Specification,
        Aixiliary
    }
    public enum SectionType
    {
        DataTypes,
        AdmittedLemmas,
        MainFunctions,
        SupportFunctions,
        AuxiliaryFunctions,
        OtherRelevantFunctions
    }
}
