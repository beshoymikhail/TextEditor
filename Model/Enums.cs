﻿ namespace TextEditor.Model
{
    public enum FunctionType
    {
        Function,
        Lemma,
        Fixpoint,
        Definition,
        Inductive,
        Record,
        Class
    }
    public enum SourceFile
    {
        Implementation,
        Specification,
        Auxiliary
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
