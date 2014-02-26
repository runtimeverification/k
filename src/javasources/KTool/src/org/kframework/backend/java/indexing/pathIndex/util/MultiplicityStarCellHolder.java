package org.kframework.backend.java.indexing.pathIndex.util;

/**
 * TODO(Owolabi): This class will be used.
 * Author: OwolabiL
 * Date: 2/4/14
 * Time: 3:17 PM
 */
public class MultiplicityStarCellHolder {
    private String parentOfCellWithMultipleK;
    private String cellWithMultipleK1;


    public void setCellWithMultipleK(String cellWithMultipleK) {
        cellWithMultipleK1 = cellWithMultipleK;
    }

    public String getParentOfCellWithMultipleK() {
        return parentOfCellWithMultipleK;
    }

    public void setParentOfCellWithMultipleK(String parentOfCellWithMultipleK) {
        this.parentOfCellWithMultipleK = parentOfCellWithMultipleK;
    }
}
