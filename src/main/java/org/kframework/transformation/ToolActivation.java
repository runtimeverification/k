package org.kframework.transformation;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.ParameterDescription;

public interface ToolActivation {

    boolean isActive(JCommander jcommander);

    public static class OptionActivation implements ToolActivation {

        private final String optionName;

        public OptionActivation(String optionName) {
            this.optionName = optionName;
        }

        @Override
        public boolean isActive(JCommander jc) {
            for (ParameterDescription param : jc.getParameters()) {
                if (param.getLongestName().equals(optionName)) {
                    Object value = param.getParameterized().get(param.getObject());
                    if (value == null) {
                        return false;
                    }
                    return !(value instanceof Boolean) || (boolean) value;
                }
            }
            return false;
        }

        @Override
        public String toString() {
            return optionName;
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result
                    + ((optionName == null) ? 0 : optionName.hashCode());
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            OptionActivation other = (OptionActivation) obj;
            if (optionName == null) {
                if (other.optionName != null)
                    return false;
            } else if (!optionName.equals(other.optionName))
                return false;
            return true;
        }

    }

    public static class OptionValueActivation<T> implements ToolActivation {

        private final String optionName;
        private final T value;

        public OptionValueActivation(String optionName, T value) {
            this.optionName = optionName;
            this.value = value;
        }

        @Override
        public boolean isActive(JCommander jc) {
            for (ParameterDescription param : jc.getParameters()) {
                if (param.getLongestName().equals(optionName)) {
                    Object value = param.getParameterized().get(param.getObject());
                    return value.equals(this.value);
                }
            }
            return false;
        }

        @Override
        public String toString() {
            return optionName + " " + value;
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result
                    + ((optionName == null) ? 0 : optionName.hashCode());
            result = prime * result + ((value == null) ? 0 : value.hashCode());
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            OptionValueActivation<?> other = (OptionValueActivation<?>) obj;
            if (optionName == null) {
                if (other.optionName != null)
                    return false;
            } else if (!optionName.equals(other.optionName))
                return false;
            if (value == null) {
                if (other.value != null)
                    return false;
            } else if (!value.equals(other.value))
                return false;
            return true;
        }
    }
}
