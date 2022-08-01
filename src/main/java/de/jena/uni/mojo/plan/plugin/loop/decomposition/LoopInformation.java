package de.jena.uni.mojo.plan.plugin.loop.decomposition;


import java.util.BitSet;
import java.util.List;

public class LoopInformation {
    public final BitSet component;
    public final BitSet doBody;
    public final BitSet cutoff;
    public final BitSet loopIn;
    public final BitSet loopOut;

    public LoopInformation(BitSet component, BitSet doBody, BitSet cutoff, BitSet loopIn, BitSet loopOut) {
        this.component = component;
        this.doBody = doBody;
        this.cutoff = cutoff;
        this.loopIn = loopIn;
        this.loopOut = loopOut;
    }
}